import Std

namespace Aethel

/-- Two four-bit logical fields represented by one byte. These are values/proxies,
not two independently addressable exclusive byte references. -/
def packNibbles (low high : Fin 16) : Nat := low.val + 16 * high.val

def lowNibble (byte : Nat) : Nat := byte % 16
def highNibble (byte : Nat) : Nat := byte / 16

def setLowNibble (byte : Nat) (value : Fin 16) : Nat :=
  value.val + 16 * highNibble byte

def setHighNibble (byte : Nat) (value : Fin 16) : Nat :=
  lowNibble byte + 16 * value.val

theorem packNibbles_fits (low high : Fin 16) : packNibbles low high < 256 := by
  simp only [packNibbles]; omega

theorem lowNibble_pack (low high : Fin 16) :
    lowNibble (packNibbles low high) = low.val := by
  simp [lowNibble, packNibbles, Nat.add_mod, Nat.mod_eq_of_lt low.isLt]

theorem highNibble_pack (low high : Fin 16) :
    highNibble (packNibbles low high) = high.val := by
  simp [highNibble, packNibbles, Nat.add_mul_div_left, Nat.div_eq_of_lt low.isLt]

theorem setLowNibble_get (byte : Nat) (value : Fin 16) :
    lowNibble (setLowNibble byte value) = value.val := by
  simp [lowNibble, setLowNibble, Nat.add_mod, Nat.mod_eq_of_lt value.isLt]

theorem setLowNibble_frame (byte : Nat) (value : Fin 16) :
    highNibble (setLowNibble byte value) = highNibble byte := by
  simp [highNibble, setLowNibble, Nat.add_mul_div_left, Nat.div_eq_of_lt value.isLt]

theorem setHighNibble_get (byte : Nat) (value : Fin 16) :
    highNibble (setHighNibble byte value) = value.val := by
  simp [highNibble, setHighNibble, lowNibble, Nat.add_mul_div_left,
    Nat.div_eq_of_lt (Nat.mod_lt byte (by decide : 0 < 16))]

theorem setHighNibble_frame (byte : Nat) (value : Fin 16) :
    lowNibble (setHighNibble byte value) = lowNibble byte := by
  simp [lowNibble, setHighNibble, Nat.add_mod]

end Aethel
