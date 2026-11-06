import Mathlib

theorem number_theory_607947 : {n : ℕ | 0 < n ∧ n < 200 ∧ IsSquare (n ^ 2 + (n + 1) ^ 2)} = {3, 20, 119} := by 
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- First, prove the forward direction: if n in left, then in right
    rintro ⟨h1, h2, h3⟩
    have h4 : n ≤ 199 := by linarith 
    by_contra h
    push_neg at h 
    have h5 : n < 200 := h2 
    interval_cases n <;> try { 
      contrapose! h3 
      native_decide 
    } <;> try { omega }
  · -- Backward implication: n ∈ {3, 20, 119} → 0 < n ∧ n < 200 ∧ IsSquare ...
    rintro (rfl | rfl | rfl)
    · -- Case n = 3 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · -- Show that 3^2 + 4^2 is a square 
        native_decide 
    · -- Case n = 20
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · -- Show that 20^2 + 21^2 is a square 
        native_decide 
    · -- Case n = 119
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · -- Show that 119^2 + 120^2 is a square 
        native_decide