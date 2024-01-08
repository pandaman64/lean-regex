import Parser

namespace Parser
variable {ε σ α β γ} [Parser.Stream σ α] [Parser.Error ε σ α] {m} [Monad m] [MonadExceptOf ε m]

@[inline]
def foldl1 (f : β → β → β) (p : ParserT ε σ α m β) : ParserT ε σ α m β := do
  let init ← p
  foldl f init p

end Parser
