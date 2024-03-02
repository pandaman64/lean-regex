import Regex.Parser
import Regex.NFA.Compile
import Regex.NFA.VM

def pushSaveStart (nfa : NFA) : NFA :=
  have inBounds : NFA.Node.inBounds (NFA.Node.save 0 nfa.start) (Array.size nfa.nodes + 1) := by
    simp [NFA.Node.inBounds]
    exact Nat.lt_trans nfa.start.isLt (Nat.lt_succ_self _)
  nfa.pushNode (.save 0 nfa.start) inBounds

def r₁ := Regex.concat (Regex.star (Regex.char 'a')) (Regex.star (Regex.char 'b'))
def NFA₁ := NFA.compile r₁
#eval NFA₁.match "aaaabbbb"
#eval NFA₁.match "ab"
#eval NFA₁.match "c"
#eval NFA₁.match ""
#eval NFA₁.search_prefix "aaaabbbb"
#eval NFA₁.search_prefix "aabbac"
#eval NFA₁.search_prefix "c"
#eval NFA₁.search_prefix ""
#eval Regex.Parser.parse! "a*b*"
def NFA₁' := NFA.compile (Regex.Parser.parse! "a*b*")
#eval NFA₁'
#eval NFA₁'.searchNext "aaaabbbb".mkIterator
#eval NFA₁'.searchNext "aabbay".mkIterator
#eval NFA₁'.searchNext "aabbx".mkIterator
#eval NFA₁'.searchNext "aabbac".mkIterator
#eval NFA₁'.searchNext "c".mkIterator
#eval NFA₁'.searchNext "".mkIterator

def r₂ := Regex.star (Regex.alternate (Regex.star (Regex.char 'a')) (Regex.char 'b'))
def NFA₂ := NFA.compile r₂
#eval NFA₂.match "aaaabbbb"
#eval NFA₂.match "abcab"
#eval NFA₂.match ""
#eval NFA₂.search_prefix "aaaabbbb"
#eval NFA₂.search_prefix "aabbac"
#eval NFA₂.search_prefix ""
def NFA₂' := NFA.compile (Regex.Parser.parse! "(a*|b)*")
#eval NFA₂'.searchNext "aaaabbbb".mkIterator
#eval NFA₂'.searchNext "aabbac".mkIterator
#eval NFA₂'.searchNext "".mkIterator

def NFA₃ := NFA.compile (Regex.alternate Regex.empty (Regex.concat (Regex.char 'a') Regex.empty))
#eval NFA₃.match ""
#eval NFA₃.match "a"
#eval NFA₃.search_prefix ""
#eval NFA₃.search_prefix "a"

def NFA₄ := NFA.compile (Regex.concat (Regex.alternate (Regex.char 'a') (Regex.char 'b')) (Regex.char 'c'))
#eval NFA₄.match "ac"
#eval NFA₄.match "bc"
#eval NFA₄.match "a"
#eval NFA₄.match ""
#eval NFA₄.search_prefix "acd"
#eval NFA₄.search_prefix "bcd"
#eval NFA₄.search_prefix "ad"
#eval NFA₄.search_prefix ""
def NFA₄' := NFA.compile (Regex.Parser.parse! "(a|b)c")
#eval NFA₄'.searchNext "ac".mkIterator
#eval NFA₄'.searchNext "bc".mkIterator
#eval NFA₄'.searchNext "a".mkIterator
#eval NFA₄'.searchNext "".mkIterator
#eval NFA₄'.searchNext "xacybc".mkIterator

def re₅ := Regex.Parser.parse! "abc(fo*|bar)*"
def NFA₅ := NFA.compile re₅
def heystack₅ := "abababxxyyabcfoooooobarfobyyyyfoobaryy"
def result₅ := NFA₅.searchNext heystack₅.mkIterator
def substr₅ := Substring.mk heystack₅ result₅.get!.1 result₅.get!.2
#eval substr₅ == "abcfoooooobarfo" -- !!!true!!!

def re₆ := Regex.Parser.parse! "abc(fo|foo)"
def NFA₆ := NFA.compile re₆
def heystack₆ := "abababcfoooo"
def result₆ := NFA₆.searchNext heystack₆.mkIterator
def substr₆ := Substring.mk heystack₆ result₆.get!.1 result₆.get!.2
#eval substr₆ == "abcfo" -- The left-most match stops at the first 'o' in "foooo"

def collect [ForIn Id ρ α] (x : ρ) : Id (Array α) := do
  let mut a := #[]
  for v in x do
    a := a.push v
  pure a

def re₇ := Regex.Parser.parse! "(q|w|e)abc"
def NFA₇ := NFA.compile re₇
def heystack₇ := "xyzxyzqabcwabcxyzxyzeabcxyzqabca"
def matches₇ := collect (NFA₇.matches heystack₇)
#eval matches₇
#eval matches₇.map (fun (x, y) => Substring.mk heystack₇ x y)
-- "qabc", "wabc", "eabc", "qabc"
