module

meta import Regex.Data.Anchor.Basic

namespace Regex.Data.Anchor.Test

-- Tests
#guard Anchor.test "".startPos .wordBoundary == false
#guard Anchor.test "".startPos .nonWordBoundary == true
#guard Anchor.test "a".startPos .wordBoundary == true
#guard Anchor.test "a".startPos .nonWordBoundary == false
#guard Anchor.test ("a".startPos.next (by decide)) .wordBoundary == true
#guard Anchor.test ("a".startPos.next (by decide)) .nonWordBoundary == false

end Regex.Data.Anchor.Test
