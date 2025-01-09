import TParser.Indexed

open TParser.Indexed

set_option autoImplicit false

namespace TParser

structure Box (α : Nat → Type) (n : Nat) where
  call : {m : Nat} → m < n → α m

namespace Box

@[inline, specialize]
def ltClose {α : Nat → Type} (closed : {m n : Nat} → m < n → α n → α m) : All (Imp α (Box α))
  | _, x => Box.mk fun h => closed h x

@[inline, specialize]
def leClose {α : Nat → Type} (closed : {m n : Nat} → m ≤ n → α n → α m) : All (Imp α (Box α))
  | _, x => Box.mk fun h => closed (Nat.le_of_lt h) x

@[inline]
def pure {α : Nat → Type} (a : All α) : All (Box α)
  | _ => Box.mk fun _ => a

@[inline]
def map {α β : Nat → Type} (f : All (Imp α β)) : All (Imp (Box α) (Box β))
  | _, ⟨call⟩ => Box.mk fun h => f (call h)

@[inline]
def app {α β : Nat → Type} : All (Imp (Box (Imp α β)) (Imp (Box α) (Box β)))
  | _, ⟨f⟩, ⟨a⟩ => Box.mk fun h => f h (a h)

@[inline]
def extract {α : Nat → Type} (a : All (Box α)) : All α
  | n => a.call (Nat.lt_succ_self n)

@[inline]
def duplicate {α : Nat → Type} : All (Imp (Box α) (Box (Box α)))
  | _, ⟨a⟩ => Box.mk fun h => Box.mk fun h' => a (Nat.lt_trans h' h)

@[inline]
def castLE {α : Nat → Type} {m n : Nat} (h : m ≤ n) (a : Box α n) : Box α m :=
  Box.mk fun h' => a.call (Nat.lt_of_lt_of_le h' h)

@[inline]
def castLT {α : Nat → Type} {m n : Nat} (h : m < n) (a : Box α n) : Box α m :=
  Box.mk fun h' => a.call (Nat.lt_trans h' h)

-- Lean can figure out the termination automatically since the Nat argument for `All` is decreasing
-- inside the `Box.mk` constructor. Besides the termination measure, the function is same as the Y combinator.
def fixBox {α : Nat → Type} (f : All (Imp (Box α) α)) : All (Box α)
  | _ => Box.mk fun _ => f (fixBox f)

@[inline]
def fix {α : Nat → Type} (f : All (Imp (Box α) α)) : All α :=
  extract (fixBox f)

end Box

end TParser
