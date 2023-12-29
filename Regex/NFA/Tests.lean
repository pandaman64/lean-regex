import Regex.NFA.Compile
import Regex.NFA.VM

def r₁ := Regex.concat (Regex.star (Regex.char 'a')) (Regex.star (Regex.char 'b'))
def NFA₁ := NFA.compile r₁
#eval NFA₁.run "aaaabbbb"
#eval NFA₁.run "ab"
#eval NFA₁.run "c"
#eval NFA₁.run ""

def r₂ := Regex.star (Regex.alternate (Regex.star (Regex.char 'a')) (Regex.char 'b'))
def NFA₂ := NFA.compile r₂
#eval NFA₂.run "aaaabbbb"
#eval NFA₂.run "abcab"
#eval NFA₁.run ""

def NFA₃ := NFA.compile (Regex.alternate Regex.empty (Regex.concat (Regex.char 'a') Regex.empty))
#eval NFA₃.run ""
#eval NFA₃.run "a"
