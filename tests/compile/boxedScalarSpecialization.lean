module

/-!
Check that a fixed type parameter in a recursive polymorphic function is
specialized when a caller supplies a scalar that would otherwise be boxed.
-/

public section

set_option compiler.check true

def genericCountdown {α : Type} : Nat → α → α
  | 0, x => x
  | n + 1, x => genericCountdown n x

/--
trace: [Compiler.specialize.step] Round: 0
[Compiler.specialize.step] Working callUInt64
[Compiler.specialize.step] new: genericCountdown._at_.callUInt64.spec_0: def genericCountdown._at_.callUInt64.spec_0 x.7 x.8 : UInt64 :=
      cases x.7 : UInt64
      | Nat.zero =>
        return x.8
      | Nat.succ n.9 =>
        let _x.10 := @genericCountdown _ n.9 x.8;
        return _x.10
[Compiler.specialize.step] Result callUInt64: def callUInt64 n x : UInt64 :=
      let _x.1 := genericCountdown._at_.callUInt64.spec_0 n x;
      return _x.1
[Compiler.specialize.step] Info for next round: [(genericCountdown._at_.callUInt64.spec_0, [O, O])]
[Compiler.specialize.step] Round: 1
[Compiler.specialize.step] Working genericCountdown._at_.callUInt64.spec_0
[Compiler.specialize.step] cached: genericCountdown._at_.callUInt64.spec_0
[Compiler.specialize.step] Result genericCountdown._at_.callUInt64.spec_0: def genericCountdown._at_.callUInt64.spec_0 x.7 x.8 : UInt64 :=
      cases x.7 : UInt64
      | Nat.zero =>
        return x.8
      | Nat.succ n.9 =>
        let _x.10 := genericCountdown._at_.callUInt64.spec_0 n.9 x.8;
        return _x.10
[Compiler.specialize.step] Working callUInt64
[Compiler.specialize.step] Result callUInt64: def callUInt64 n x : UInt64 :=
      let _x.1 := genericCountdown._at_.callUInt64.spec_0 n x;
      return _x.1
[Compiler.specialize.step] Info for next round: [(genericCountdown._at_.callUInt64.spec_0, [O, O])]
[Compiler.specialize.step] Round: 2
[Compiler.specialize.step] Working genericCountdown._at_.callUInt64.spec_0
[Compiler.specialize.step] Result genericCountdown._at_.callUInt64.spec_0: def genericCountdown._at_.callUInt64.spec_0 x.7 x.8 : UInt64 :=
      cases x.7 : UInt64
      | Nat.zero =>
        return x.8
      | Nat.succ n.9 =>
        let _x.10 := genericCountdown._at_.callUInt64.spec_0 n.9 x.8;
        return _x.10
[Compiler.specialize.step] Info for next round: [(genericCountdown._at_.callUInt64.spec_0, [O, O])]
[Compiler.specialize.step] Termination after 3 rounds
-/
#guard_msgs in
set_option trace.Compiler.specialize.step true in
def callUInt64 (n : Nat) (x : UInt64) : UInt64 := genericCountdown n x

def callUSize (n : Nat) (x : USize) : USize := genericCountdown n x

def callFloat (n : Nat) (x : Float) : Float := genericCountdown n x

def callFloat32 (n : Nat) (x : Float32) : Float32 := genericCountdown n x

def callNat (n : Nat) (x : Nat) : Nat := genericCountdown n x

def main : IO Unit := do
  for n in [0:25] do
    unless callUInt64 n 0x123456789abcdef0 == 0x123456789abcdef0 do
      throw <| IO.userError "UInt64 specialization mismatch"
    unless callUSize n 123456 == 123456 do
      throw <| IO.userError "USize specialization mismatch"
    unless callFloat n 1.25 == 1.25 do
      throw <| IO.userError "Float specialization mismatch"
    unless callFloat32 n 1.25 == 1.25 do
      throw <| IO.userError "Float32 specialization mismatch"
    unless callNat n 123456 == 123456 do
      throw <| IO.userError "Nat specialization mismatch"
  IO.println "boxed scalar specialization: ok"
