module

/-!
Check that an `Option` list accumulator can be consumed as a scalar without
allocating a final `some` value.
-/

public section

set_option compiler.check true

def lastByte : List UInt8 → Option UInt8 → Option UInt8
  | [], last => last
  | x :: xs, _ => lastByte xs (some x)

/--
trace: [Compiler.saveMono] size: 5
    def scanToByte xs : UInt8 :=
      cases xs : UInt8
      | List.nil =>
        let _x.1 := 0;
        return _x.1
      | List.cons head tail =>
        let result := lastByte._optionAccumulatorWorker tail head;
        return result
-/
#guard_msgs in
set_option trace.Compiler.saveMono true in
def scanToByte (xs : List UInt8) : UInt8 := (lastByte xs none).getD 0

def main : IO Unit := do
  unless scanToByte [] == 0 && scanToByte [3] == 3 &&
      scanToByte [1, 2, 255] == 255 do
    throw <| IO.userError "consumed option mismatch"
  IO.println "consumed option: ok"
