import Regex

def main : IO Unit := do
  -- Search/replace the first match
  let phoneNumber := Regex.parse! r#"\d+-\d+-\d+"#
  let haystack := "こんにちは0120-333-906🤗Lotus123"

  -- prints: (some (15, 27)) -> 0120-333-906
  let pos := phoneNumber.find haystack
  IO.println s!"{pos} -> {Substring.mk haystack pos.get!.1 pos.get!.2}"

  -- prints: こんにちは[redacted]🤗Lotus123
  let replaced := phoneNumber.replace haystack "[redacted]"
  IO.println replaced

  -- Search/replace all non-overlapping matches
  -- The re! literal checks for regex errors at compile time and creates a compiled `Regex` object
  let regex := re!"もも"
  let haystack := "すもももももももものうち"

  -- prints: #[(3, 9), (9, 15), (15, 21), (21, 27)]
  let allMatches := regex.findAll haystack
  IO.println allMatches

  -- prints: す🍑🍑🍑🍑のうち
  let replaced := regex.replaceAll haystack "🍑"
  IO.println replaced

-- Bad sharing of the updates buffer resulted in a bug. The following regex shouldn't report
-- the indices for the inner parenthesis.
def re := re! "(?:c()|)c"
/--
info: #[{ buffer := #[some { byteIdx := 0 }, some { byteIdx := 1 }, none, none] }]
-/
#guard_msgs in
#eval re.captureAll "c"
