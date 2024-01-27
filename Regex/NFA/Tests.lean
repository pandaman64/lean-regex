import Regex.NFA.Compile
import Regex.NFA.VM

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

def r₂ := Regex.star (Regex.alternate (Regex.star (Regex.char 'a')) (Regex.char 'b'))
def NFA₂ := NFA.compile r₂
#eval NFA₂.match "aaaabbbb"
#eval NFA₂.match "abcab"
#eval NFA₂.match ""
#eval NFA₂.search_prefix "aaaabbbb"
#eval NFA₂.search_prefix "aabbac"
#eval NFA₂.search_prefix ""

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
