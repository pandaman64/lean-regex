import Regex.Regex.Iterators.Captures

open Std.Iterators (Iter IterM)

def Regex.matchesM (regex : Regex) (haystack : String) (m : Type → Type w) [Monad m] :=
  (regex.capturesM haystack m (bufferSize := 2)
  |>.filterMap fun groups => groups.get 0
  : IterM m Substring)

def Regex.matches (regex : Regex) (haystack : String) :=
  ((matchesM regex haystack Id).toIter : Iter Substring)
