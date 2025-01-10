import TParser.Indexed

set_option autoImplicit false

open String (Iterator)
open TParser.Indexed

namespace TParser

structure Success (α : Type) (n : Nat) where
  val : α
  it : Iterator
  lt : it.remainingBytes < n

def Success.mk' {α : Type} {it it' : Iterator}
  (val : α) (h : it'.remainingBytes < it.remainingBytes) : Success α it.remainingBytes :=
  ⟨val, it', h⟩

namespace Success

def remainingBytes {α n} (s : Success α n) : Nat := s.it.remainingBytes

def castLE {α m n} (h : m ≤ n) (s : Success α m) : Success α n :=
  ⟨s.val, s.it, Nat.lt_of_lt_of_le s.lt h⟩

def castLT {α m n} (h : m < n) (s : Success α m) : Success α n :=
  ⟨s.val, s.it, Nat.lt_trans s.lt h⟩

def map {α β} (f : α → β) : All (Imp (Success α) (Success β))
  | _, ⟨val, it', h⟩ => ⟨f val, it', h⟩

def mapConst {α β} (a : α) : All (Imp (Success β) (Success α))
  | _, ⟨_, it', h⟩ => ⟨a, it', h⟩

def mapD {α β} (f : α → Option β) (default : β) : All (Imp (Success α) (Success β))
  | _, ⟨val, it', h⟩ => ⟨(f val).getD default, it', h⟩

def guardM {α β} (f : α → Option β) : All (Imp (Success α) (App Option (Success β)))
  | _, ⟨val, it', h⟩ => (f val).map (fun val' => ⟨val', it', h⟩)

def and {α β n} (p : Success α n) (q : Success β p.remainingBytes) : Success (α × β) n :=
  ⟨(p.val, q.val), q.it, Nat.lt_trans q.lt p.lt⟩

end Success

end TParser
