import Mathlib

theorem algebra_143965 (u v : ℝ) (hu : u = 1.5) (hv : v = 3)
    (h : u + v = 2 * v / 3 + u) (l : ℝ) (hl : l = 100) :
    l / (u + v) = 10 := by
  rw [hv] at h
  rw [hu] at h
  norm_num at h
  all_goals
    try { 
      rw [hl, hu, hv]
      norm_num at h ⊢ 
      <;> try { linarith }
      <;> try { tauto }
      <;> try { norm_num }
    }
    <;> try { contradiction }
    <;> try { linarith }
    <;> try { tauto }
    <;> try { norm_num }