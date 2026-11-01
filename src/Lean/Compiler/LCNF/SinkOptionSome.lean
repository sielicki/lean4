/-
Copyright (c) 2026 Nicholas Sielicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.DependsOn

public section

namespace Lean.Compiler.LCNF

private partial def sinkSome (decl : LetDecl .pure) (code : Code .pure) :
    CompilerM (Code .pure) := do
  let target := ({} : FVarIdSet).insert decl.fvarId
  let used := code.dependsOn target
  if !used then return code
  match code with
  | .let next k =>
    if next.dependsOn target then
      return .let decl code
    return .let next (← sinkSome decl k)
  | .cases cases =>
    if cases.discr == decl.fvarId || cases.resultType.containsFVar decl.fvarId then
      return .let decl code
    let alts ← cases.alts.mapM fun alt => do
      return alt.updateCode (← sinkSome decl alt.getCode)
    return code.updateAlts! alts
  | .jp joinPoint k =>
    if !k.dependsOn target &&
        !joinPoint.type.containsFVar decl.fvarId &&
        !joinPoint.params.any (fun p => p.type.containsFVar decl.fvarId) then
      let value ← sinkSome decl joinPoint.value
      let joinPoint ← joinPoint.updateValue value
      return code.updateFun! joinPoint k
    return .let decl code
  | _ =>
    let replacement ← mkLetDecl decl.binderName decl.type decl.value
    let subst : FVarSubst .pure := ({} : FVarSubst .pure).insert decl.fvarId (.fvar replacement.fvarId)
    return .let replacement (← replaceFVars code subst false)

private partial def sinkOptionSomeCode (code : Code .pure) : CompilerM (Code .pure) := do
  match code with
  | .let decl k =>
    let k ← sinkOptionSomeCode k
    if let .const ``Option.some [] #[_, _] := decl.value then
      if !decl.type.isAppOf ``Option then return code.updateCont! k
      return ← sinkSome decl k
    return code.updateCont! k
  | .cases cases =>
    let alts ← cases.alts.mapM fun alt => do
      return alt.updateCode (← sinkOptionSomeCode alt.getCode)
    return code.updateAlts! alts
  | .fun decl k | .jp decl k =>
    let value ← sinkOptionSomeCode decl.value
    let decl ← decl.updateValue value
    return code.updateFun! decl (← sinkOptionSomeCode k)
  | _ => return code

private def sinkOptionSomeDecl (decl : Decl .pure) : CompilerM (Decl .pure) := do
  let value ← decl.value.mapCodeM sinkOptionSomeCode
  return { decl with value }

/-- Delay constructing `Option.some` until the control-flow path that uses it. -/
def sinkOptionSome : Pass :=
  .mkPerDeclaration `sinkOptionSome .mono sinkOptionSomeDecl

end Lean.Compiler.LCNF
