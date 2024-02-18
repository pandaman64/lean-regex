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
def NFA₁' := pushSaveStart NFA₁
#eval NFA₁'.search' "aaaabbbb" 1
#eval NFA₁'.search' "aabbac" 1
#eval NFA₁'.search' "c" 1
#eval NFA₁'.search' "" 1

def r₂ := Regex.star (Regex.alternate (Regex.star (Regex.char 'a')) (Regex.char 'b'))
def NFA₂ := NFA.compile r₂
#eval NFA₂.match "aaaabbbb"
#eval NFA₂.match "abcab"
#eval NFA₂.match ""
#eval NFA₂.search_prefix "aaaabbbb"
#eval NFA₂.search_prefix "aabbac"
#eval NFA₂.search_prefix ""
def NFA₂' := pushSaveStart NFA₂
#eval NFA₂'.search' "aaaabbbb" 1
#eval NFA₂'.search' "aabbac" 1
#eval NFA₂'.search' "" 1

def NFA₃ := NFA.compile (Regex.alternate Regex.empty (Regex.concat (Regex.char 'a') Regex.empty))
#eval NFA₃.match ""
#eval NFA₃.match "a"
#eval NFA₃.search_prefix ""
#eval NFA₃.search_prefix "a"
def NFA₃' := pushSaveStart NFA₃
#eval NFA₃'.search' "" 1
#eval NFA₃'.search' "a" 1

def NFA₄ := NFA.compile (Regex.concat (Regex.alternate (Regex.char 'a') (Regex.char 'b')) (Regex.char 'c'))
#eval NFA₄.match "ac"
#eval NFA₄.match "bc"
#eval NFA₄.match "a"
#eval NFA₄.match ""
#eval NFA₄.search_prefix "acd"
#eval NFA₄.search_prefix "bcd"
#eval NFA₄.search_prefix "ad"
#eval NFA₄.search_prefix ""
def NFA₄' := pushSaveStart NFA₄
#eval NFA₄'.search' "ac" 1
#eval NFA₄'.search' "bc" 1
#eval NFA₄'.search' "a" 1
#eval NFA₄'.search' "" 1
#eval NFA₄'.search' "xacybc" 1

def re₅ := Regex.Parser.parse! "abc(fo*|bar)*"
def NFA₅ := pushSaveStart (NFA.compile re₅)
def heystack₅ := "abababxxyyabcfoooooobarfobyyyyfoobaryy"
def result₅ := NFA₅.search' heystack₅ 1
def substr₅ := Substring.mk heystack₅ result₅.get!.1[0]!.get! result₅.get!.2
#eval substr₅ == "abcfoooooobarfo" -- !!!true!!!

def re₆ := Regex.Parser.parse! "abc(fo|foo)"
def NFA₆ := pushSaveStart (NFA.compile re₆)
def heystack₆ := "abababcfoooo"
def result₆ := NFA₆.search' heystack₆ 1
def substr₆ := Substring.mk heystack₆ result₆.get!.1[0]!.get! result₆.get!.2
#eval substr₆ == "abcfo" -- The left-most match stops at the first 'o' in "foooo"
