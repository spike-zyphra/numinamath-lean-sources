import Mathlib

/- Cassandra sets her watch to the correct time at noon. At the actual time of 1:00 PM, she notices that her watch 
reads 12:57 and 36 seconds. Assuming that her watch loses time at a constant rate, what will be the actual time when 
her watch first reads 10:00 PM?
(A) 10:22 PM and 24 seconds(B) 10:24 PM(C) 10:25 PM(D) 10:27 PM(E) 10:30 PM-/

-- After transferring this statement into an equation, it becomes a simple calculation, rearranging the hypothesis.
theorem algebra_96338  (x : ℝ) (hx : x > 0) (h : (60 * 57 + 36) / (60 * 60) = (10 * 60 * 60) / x) :
x = (60 * 10 + 25)*60 := by {
  have h' : 3456 * x = 129600000 := by { 
    field_simp at h
    norm_num at h
    exact h
    }
  calc x = 3456 * x / 3456 := by norm_num
       _ = 129600000 / 3456 := by rw [h']
       _ = (60 * 10 + 25)*60 := by norm_num
}