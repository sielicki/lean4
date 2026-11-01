module

/-!
Check the `Option UInt8` loop state used by byte stream transducers.
-/

public section

set_option compiler.check true

def scanBytes (input : ByteArray) (initial : Option UInt8) : Option UInt8 := Id.run do
  let mut state := initial
  for byte in input do
    if byte == 0 then continue
    if state == some byte then continue
    state := some byte
  return state

/--
trace: [Compiler.saveMono] size: 32
    def ByteArray.forInUnsafe.loop._at_.scanAndCopy.spec_0 as sz i b : Prod (Option UInt8) ByteArray :=
      jp _jp.1 a.2 : Prod (Option UInt8) ByteArray :=
        let _x.3 := 1;
        let _x.4 := USize.add i _x.3;
        let _x.5 := ByteArray.forInUnsafe.loop._at_.scanAndCopy.spec_0 as sz _x.4 a.2;
        return _x.5;
      let _x.6 := USize.decLt i sz;
      cases _x.6 : Prod (Option UInt8) ByteArray
      | Bool.false =>
        return b
      | Bool.true =>
        cases b : Prod (Option UInt8) ByteArray
        | Prod.mk fst snd =>
          let a := @ByteArray.uget as i ◾;
          jp _jp.7 : Prod (Option UInt8) ByteArray :=
            let output := ByteArray.push snd a;
            let state := some ◾ a;
            let _x.8 := Prod.mk ◾ ◾ state output;
            goto _jp.1 _x.8;
          let _x.9 := 0;
          let _x.10 := UInt8.decEq a _x.9;
          cases _x.10 : Prod (Option UInt8) ByteArray
          | Bool.false =>
            cases fst : Prod (Option UInt8) ByteArray
            | Option.none =>
              goto _jp.7
            | Option.some val.11 =>
              let _x.12 := UInt8.decEq val.11 a;
              cases _x.12 : Prod (Option UInt8) ByteArray
              | Bool.false =>
                goto _jp.7
              | Bool.true =>
                let _x.13 := Prod.mk ◾ ◾ fst snd;
                goto _jp.1 _x.13
          | Bool.true =>
            let _x.14 := Prod.mk ◾ ◾ fst snd;
            goto _jp.1 _x.14
[Compiler.saveMono] size: 8
    def scanAndCopy input initial : Prod (Option UInt8) ByteArray :=
      let output := ByteArray.empty;
      let _x.1 := Prod.mk ◾ ◾ initial output;
      let sz := ByteArray.usize input;
      let _x.2 := 0;
      let _x.3 := ByteArray.forInUnsafe.loop._at_.scanAndCopy.spec_0 input sz _x.2 _x.1;
      cases _x.3 : Prod (Option UInt8) ByteArray
      | Prod.mk fst snd =>
        let _x.4 := Prod.mk ◾ ◾ fst snd;
        return _x.4
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
def scanAndCopy (input : ByteArray) (initial : Option UInt8) : Option UInt8 × ByteArray :=
  Id.run do
    let mut state := initial
    let mut output := ByteArray.empty
    for byte in input do
      if byte == 0 then continue
      if state == some byte then continue
      output := output.push byte
      state := some byte
    return (state, output)

def main : IO Unit := do
  unless scanBytes ⟨#[0, 1, 1, 2]⟩ none == some 2 &&
      scanBytes ⟨#[]⟩ (some 7) == some 7 &&
      scanAndCopy ⟨#[0, 1, 1, 2]⟩ none == (some 2, ⟨#[1, 2]⟩) do
    throw <| IO.userError "option byte loop mismatch"
  IO.println "option byte loop: ok"
