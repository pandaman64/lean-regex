import Regex.Syntax.Parser
import Regex.NFA.Compile
import Regex.NFA.VM

open Regex.Syntax.Parser

def collect [ForIn Id ρ α] (x : ρ) : Id (Array α) := do
  let mut a := #[]
  for v in x do
    a := a.push v
  pure a

def NFA₁ := NFA.compile (parse! "a*b*")
#eval NFA₁
#eval NFA₁.searchNext "aaaabbbb".mkIterator
#eval NFA₁.searchNext "aabbay".mkIterator
#eval NFA₁.searchNext "aabbx".mkIterator
#eval NFA₁.searchNext "aabbac".mkIterator
#eval NFA₁.searchNext "c".mkIterator
#eval NFA₁.searchNext "".mkIterator

def NFA₂ := NFA.compile (parse! "(a*|b)*")
#eval NFA₂.searchNext "aaaabbbb".mkIterator
#eval NFA₂.searchNext "aabbac".mkIterator
#eval NFA₂.searchNext "".mkIterator

def NFA₃ := NFA.compile (Regex.alternate Regex.empty (Regex.concat (Regex.char 'a') Regex.empty))
#eval NFA₃.searchNext "".mkIterator
#eval NFA₃.searchNext "a".mkIterator

def NFA₄ := NFA.compile (parse! "(a|b)c")
#eval NFA₄.searchNext "ac".mkIterator
#eval NFA₄.searchNext "bc".mkIterator
#eval NFA₄.searchNext "a".mkIterator
#eval NFA₄.searchNext "".mkIterator
#eval NFA₄.searchNext "xacybc".mkIterator

def re₅ := parse! "abc(fo*|bar)*"
def NFA₅ := NFA.compile re₅
def heystack₅ := "abababxxyyabcfoooooobarfobyyyyfoobaryy"
def result₅ := NFA₅.searchNext heystack₅.mkIterator
def substr₅ := Substring.mk heystack₅ result₅.get!.1 result₅.get!.2
#eval substr₅ == "abcfoooooobarfo" -- !!!true!!!

def re₆ := parse! "abc(fo|foo)"
def NFA₆ := NFA.compile re₆
def heystack₆ := "abababcfoooo"
def result₆ := NFA₆.searchNext heystack₆.mkIterator
def substr₆ := Substring.mk heystack₆ result₆.get!.1 result₆.get!.2
#eval substr₆ == "abcfo" -- The left-most match stops at the first 'o' in "foooo"

def re₇ := parse! "(q|w|e)abc"
def NFA₇ := NFA.compile re₇
def heystack₇ := "xyzxyzqabcwabcxyzxyzeabcxyzqabca"
def matches₇ := collect (NFA₇.matches heystack₇)
#eval matches₇
#eval matches₇.map (fun (x, y) => Substring.mk heystack₇ x y)
-- "qabc", "wabc", "eabc", "qabc"
