import Regex

def main : IO Unit := do
  -- まだ+を実装してないです…
  let digits := Regex.parse! "[0-9][0-9]*"
  let haystack := "こんにちは0120-333-906🤗Lotus123"

  -- prints:
  -- (15, 19) -> 0120
  -- (20, 23) -> 333
  -- (24, 27) -> 906
  -- (36, 39) -> 123
  let results := digits.findAll haystack
  for result in results do
    IO.println s!"{result} -> {Substring.mk haystack result.1 result.2}"

  -- prints: こんにちは[redacted]-[redacted]-[redacted]🤗Lotus[redacted]
  let replaced := digits.replaceAll haystack "[redacted]"
  IO.println replaced
