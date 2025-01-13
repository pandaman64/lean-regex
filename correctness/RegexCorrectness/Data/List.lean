set_option autoImplicit false

def List.ofOption {α} : Option α → List α
  | none => []
  | some x => [x]

def List.consOption {α} : Option α → List α → List α
  | none, xs => xs
  | some x, xs => x :: xs

infixr:67 " ::ₒ " => List.consOption

@[simp]
theorem List.ofOption_none {α} : @List.ofOption α .none = [] := rfl

@[simp]
theorem List.ofOption_some {α} (x : α) : List.ofOption (some x) = [x] := rfl

@[simp]
theorem List.consOption_none {α} (xs : List α) : none ::ₒ xs = xs := rfl

@[simp]
theorem List.consOption_some {α} (x : α) (xs : List α) : some x ::ₒ xs = x :: xs := rfl

@[simp]
theorem List.ofOption_append {α} (opt : Option α) (xs : List α) :
  List.ofOption opt ++ xs = opt ::ₒ xs := by
  cases opt <;> simp

@[simp]
theorem List.consOption_append {α} (opt : Option α) (xs ys : List α) :
  opt ::ₒ xs ++ ys = opt ::ₒ (xs ++ ys) := by
  cases opt <;> simp

@[simp]
theorem List.consOption_nil {α} (opt : Option α) : opt ::ₒ [] = List.ofOption opt := by
  cases opt <;> simp
