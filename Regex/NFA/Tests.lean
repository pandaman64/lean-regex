import Regex.NFA.Compile
import Regex.NFA.VM

def r₁ := Regex.concat (Regex.star (Regex.char 'a')) (Regex.star (Regex.char 'b'))
def NFA₁ := NFA.compile r₁
#eval NFA₁.match "aaaabbbb"
#eval NFA₁.match "ab"
#eval NFA₁.match "c"
#eval NFA₁.match ""

def r₂ := Regex.star (Regex.alternate (Regex.star (Regex.char 'a')) (Regex.char 'b'))
def NFA₂ := NFA.compile r₂
#eval NFA₂.match "aaaabbbb"
#eval NFA₂.match "abcab"
#eval NFA₁.match ""

def NFA₃ := NFA.compile (Regex.alternate Regex.empty (Regex.concat (Regex.char 'a') Regex.empty))
#eval NFA₃.match ""
#eval NFA₃.match "a"
