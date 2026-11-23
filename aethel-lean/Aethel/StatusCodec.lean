import Std

namespace Aethel

/-- Concrete ADT example from the language proposal, independent of surface syntax. -/
inductive Status where
  | idle
  | moving (speedClass : Fin 4)
  | poisoned (ticks : Fin 16)
  | dead
  deriving Repr, DecidableEq

/-- Two discriminator bits followed by up to four constructor payload bits. -/
def Status.encode : Status → Nat
  | .idle => 0
  | .moving speed => 1 + 4 * speed.val
  | .poisoned ticks => 2 + 4 * ticks.val
  | .dead => 3

def Status.decode (bits : Nat) : Option Status :=
  match bits % 4 with
  | 0 => if bits / 4 = 0 then some .idle else none
  | 1 => if h : bits / 4 < 4 then some (.moving ⟨bits / 4, h⟩) else none
  | 2 => if h : bits / 4 < 16 then some (.poisoned ⟨bits / 4, h⟩) else none
  | 3 => if bits / 4 = 0 then some .dead else none
  | _ => none

theorem Status.encode_fits (status : Status) : status.encode < 64 := by
  cases status <;> simp only [Status.encode] <;> omega

theorem Status.decode_encode (status : Status) : Status.decode status.encode = some status := by
  cases status with
  | idle => rfl
  | dead => rfl
  | moving speed =>
    simp [Status.encode, Status.decode, Nat.add_mul_div_left, speed.isLt]
  | poisoned ticks =>
    simp [Status.encode, Status.decode, Nat.add_mul_div_left, ticks.isLt]

theorem Status.encode_injective {a b : Status} (h : a.encode = b.encode) : a = b := by
  simpa only [Status.decode_encode, Option.some.injEq] using congrArg Status.decode h

end Aethel
