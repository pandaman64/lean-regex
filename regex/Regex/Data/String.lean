namespace String.Iterator

@[simp]
theorem next'_remainingBytes_lt {it : Iterator} {h : it.hasNext} : (it.next' h).remainingBytes < it.remainingBytes := by
  simp [hasNext] at h
  simp [next', remainingBytes, String.next]
  have : (it.s.get it.i).utf8Size > 0 := Char.utf8Size_pos _
  omega

end String.Iterator
