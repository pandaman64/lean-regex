namespace TParser.Indexed

def Imp (α β : Nat → Type) (n : Nat) : Type := α n → β n

def And (α β : Nat → Type) (n : Nat) : Type := α n × β n

def Or (α β : Nat → Type) (n : Nat) : Type := α n ⊕ β n

def App (f : Type → Type) (α : Nat → Type) (n : Nat) : Type := f (α n)

def Const (α : Type) (_ : Nat) : Type := α

-- Should n be {n} or lazy one?
def All (α : Nat → Type) : Type := ∀ {n}, α n

end TParser.Indexed
