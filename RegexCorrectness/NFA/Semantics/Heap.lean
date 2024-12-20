set_option autoImplicit false

namespace Regex.NFA.Semantics

def Heap := Nat → Option String.Pos

namespace Heap

def lookup (heap : Heap) (i : Nat) : Option String.Pos :=
  heap i

def contains (heap : Heap) (i : Nat) : Bool :=
  (heap i).isSome

def insert (heap : Heap) (i : Nat) (pos : String.Pos) : Heap :=
  fun j => if i = j then some pos else heap j

notation:max heap:max "[" i:70 " := " pos:70 "]" => Heap.insert heap i pos

instance : EmptyCollection Heap where
  emptyCollection := fun _ => none

instance : GetElem? Heap Nat String.Pos (fun heap i => heap.contains i) where
  getElem heap i h := (heap.lookup i).get h
  getElem? heap i := heap.lookup i

theorem getElem?_insert {heap : Heap} {i j : Nat} {pos : String.Pos} :
  heap[i := pos][j]? = if i = j then .some pos else heap[j]? := rfl

end Heap

end Regex.NFA.Semantics
