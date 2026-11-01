/-
Copyright (c) 2026 Nicholas Sielicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.InferType

public section

namespace Lean.Compiler.LCNF

/--
Recognize a tail-recursive list loop whose `Option` accumulator is only
returned at the end or replaced by `some head` before the recursive call.
The original declaration handles the empty list and calls a worker for a
nonempty list. The worker carries and returns the last element directly.
The original declaration constructs `some` only when its result escapes.
-/
private def optionAccumulatorWorker? (decl : Decl .pure) :
    CompilerM (Option (Array (Decl .pure))) := do
  unless decl.recursive do return none
  let #[list, acc] := decl.params | return none
  let .app (.const ``List _) payloadType := list.type | return none
  let optionType := mkApp (mkConst ``Option) payloadType
  unless acc.type == optionType do
    return none
  let .code (.cases cases) := decl.value | return none
  unless cases.typeName == ``List && cases.discr == list.fvarId &&
      cases.resultType == optionType do return none
  let #[nilAlt, consAlt] := cases.alts | return none
  let .alt nilName nilParams nilCode := nilAlt | return none
  let .return nilResult := nilCode | return none
  unless nilName == ``List.nil && nilParams.isEmpty && nilResult == acc.fvarId do return none
  let .alt consName consParams consCode := consAlt | return none
  unless consName == ``List.cons do return none
  let #[head, tail] := consParams | return none
  unless head.type == payloadType && tail.type == list.type do return none
  let .let someDecl (.let recDecl (.return result)) := consCode | return none
  let .const ``Option.some someLevels someArgs := someDecl.value | return none
  let #[someTypeArg, .fvar somePayload] := someArgs | return none
  unless someLevels.isEmpty && somePayload == head.fvarId &&
      someDecl.type == optionType do return none
  let .const recName recLevels recArgs := recDecl.value | return none
  let #[.fvar recList, .fvar recAcc] := recArgs | return none
  unless recName == decl.name && recLevels.isEmpty &&
      recList == tail.fvarId && recAcc == someDecl.fvarId &&
      result == recDecl.fvarId && recDecl.type == optionType do return none

  let workerName := decl.name ++ `_optionAccumulatorWorker
  -- A user declaration may already have the generated name.
  if (← getEnv).contains workerName || (← getDecl? workerName).isSome then
    return none
  let payload ← mkParam `payload payloadType false
  let workerParams := #[list, payload]
  let workerType ← mkForallParams workerParams payloadType
  let recWork ← mkLetDecl `recResult payloadType
    (.const workerName [] #[.fvar tail.fvarId, .fvar head.fvarId])
  let workerCode : Code .pure := .cases ⟨``List, payloadType, list.fvarId, #[
    .alt ``List.nil #[] (.return payload.fvarId),
    .alt ``List.cons consParams (.let recWork (.return recWork.fvarId))
  ]⟩
  let worker : Decl .pure := {
    decl with
    name := workerName
    type := workerType
    params := workerParams
    value := .code workerCode
    inlineAttr? := none
  }

  let wrapperResult ← mkLetDecl `result payloadType
    (.const workerName [] #[.fvar tail.fvarId, .fvar head.fvarId])
  let wrapperSome ← mkLetDecl `someResult optionType
    (.const ``Option.some [] #[someTypeArg, .fvar wrapperResult.fvarId])
  let wrapperCode : Code .pure := .cases ⟨``List, optionType, list.fvarId, #[
    .alt ``List.nil #[] (.return acc.fvarId),
    .alt ``List.cons consParams
      (.let wrapperResult (.let wrapperSome (.return wrapperSome.fvarId)))
  ]⟩
  let wrapper := { decl with value := .code wrapperCode, recursive := false }
  worker.saveMono
  wrapper.saveMono
  return some #[worker, wrapper]

private def consumedOptionResult? (decl : Decl .pure) :
    CompilerM (Option (Decl .pure)) := do
  let .code (.let noneDecl (.let callDecl (.cases cases))) := decl.value | return none
  let .const ``Option.none [] #[_] := noneDecl.value | return none
  let .const callee [] #[.fvar xs, .fvar initial] := callDecl.value | return none
  unless initial == noneDecl.fvarId do return none
  let .app (.const ``Option _) payloadType := noneDecl.type | return none
  let workerName := callee ++ `_optionAccumulatorWorker
  let some ⟨.pure, worker⟩ ← getDecl? workerName | return none
  let #[list, payload] := worker.params | return none
  let .code (.cases workerCases) := worker.value | return none
  let #[.alt ``List.nil #[] (.return workerNil),
      .alt ``List.cons #[workerHead, workerTail]
        (.let workerCall (.return workerResult))] := workerCases.alts | return none
  let .const workerCallee [] #[.fvar callTail, .fvar callHead] := workerCall.value
    | return none
  unless worker.recursive && workerCases.typeName == ``List &&
      workerCases.discr == list.fvarId && workerCases.resultType == payloadType &&
      workerNil == payload.fvarId && workerCallee == workerName &&
      callTail == workerTail.fvarId && callHead == workerHead.fvarId &&
      workerResult == workerCall.fvarId do return none
  unless list.type == mkApp (mkConst ``List) payloadType &&
      payload.type == payloadType && callDecl.type == mkApp (mkConst ``Option) payloadType &&
      cases.typeName == ``Option && cases.discr == callDecl.fvarId &&
      cases.resultType == payloadType do return none
  let #[.alt ``Option.none #[] nilCode, .alt ``Option.some #[value] someCode] := cases.alts
    | return none
  let .return someResult := someCode | return none
  unless someResult == value.fvarId && value.type == payloadType do return none
  let head ← mkParam `head payloadType false
  let tail ← mkParam `tail list.type false
  let result ← mkLetDecl `result payloadType
    (.const workerName [] #[.fvar tail.fvarId, .fvar head.fvarId])
  let code : Code .pure := .cases ⟨``List, payloadType, xs, #[
    .alt ``List.nil #[] nilCode,
    .alt ``List.cons #[head, tail] (.let result (.return result.fvarId))
  ]⟩
  let replacement := { decl with value := .code code }
  replacement.saveMono
  return some replacement

private def runOptionAccumulatorWorker (decls : Array (Decl .pure)) :
    CompilerM (Array (Decl .pure)) := do
  decls.foldlM (init := #[]) fun result decl => do
    let replacement ← optionAccumulatorWorker? decl
    match replacement with
    | some workerAndWrapper => return result ++ workerAndWrapper
    | none => return result.push ((← consumedOptionResult? decl).getD decl)

/-- Carry a simple list loop's `Option` accumulator as its payload. -/
def optionAccumulatorWorker : Pass where
  name := `optionAccumulatorWorker
  phase := .mono
  phaseOut := .mono
  run := runOptionAccumulatorWorker

end Lean.Compiler.LCNF
