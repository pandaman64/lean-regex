import Regex.NFA.Compile
import Regex.NFA.VM

def r₁ := Regex.concat (Regex.star (Regex.char 'a')) (Regex.star (Regex.char 'b'))
def NFA₁ := NFA.compile r₁
def inBounds₁ : NFA₁.inBounds := NFA.compile.inBounds rfl
#eval NFA₁.match inBounds₁ "aaaabbbb"
#eval NFA₁.match inBounds₁ "ab"
#eval NFA₁.match inBounds₁ "c"
#eval NFA₁.match inBounds₁ ""

def r₂ := Regex.star (Regex.alternate (Regex.star (Regex.char 'a')) (Regex.char 'b'))
def NFA₂ := NFA.compile r₂
def inBounds₂ : NFA₂.inBounds := NFA.compile.inBounds rfl
#eval NFA₂.match inBounds₂ "aaaabbbb"
#eval NFA₂.match inBounds₂ "abcab"
#eval NFA₂.match inBounds₂ ""

def NFA₃ := NFA.compile (Regex.alternate Regex.empty (Regex.concat (Regex.char 'a') Regex.empty))
def inBounds₃ : NFA₃.inBounds := NFA.compile.inBounds rfl
#eval NFA₃.match inBounds₃ ""
#eval NFA₃.match inBounds₃ "a"
