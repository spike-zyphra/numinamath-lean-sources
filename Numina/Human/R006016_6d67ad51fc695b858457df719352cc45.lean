import Mathlib

/- A broken calculator has the + and $\times$ keys switched. For how many ordered pairs
  $(a, b)$ of integers will it correctly calculate $a+b$ using the labelled + key? -/
theorem number_theory_611121 : {(a, b) : ℤ × ℤ | a + b = a * b}.encard = 2 := by
  transitivity ({(0, 0), (2, 2)} : Set (ℤ × ℤ)).encard
  · congr 1
    /- The set is exatly `{(0, 0), (2, 2)}`. -/
    ext ⟨a, b⟩
    simp
    refine ⟨fun h => ?_, fun h => ?_⟩
    · /- From `a + b = ab`, we prove that `(b - 1) * (a - 1) = 1`. -/
      have eq : (b - 1) * (a - 1) = 1 := by
        rw [← sub_eq_zero] at h ⊢
        rw [← neg_inj]
        convert h using 1
        ring
      /- So `b - 1 ∣ 1`, then `b` must be 0 or 2. -/
      have hb : b - 1 ∣ 1 := ⟨_, eq.symm⟩
      rw [← isUnit_iff_dvd_one, Int.isUnit_iff] at hb
      /- So `a` is 0 or 2 respectively. -/
      cases' hb with hb hb <;> (rw [hb] at eq; omega)
    · /- If `(a, b)` is `(0, 0)` or `(2, 2)`, it satisfies the condition. -/
      cases' h with h h <;> simp [h]
  · /- Prove that the cardinality of `{(0, 0), (2, 2)}` is 2. -/
    rw [Set.encard_insert_of_not_mem]
    · norm_num
    · intro h
      simp only [Set.mem_singleton_iff] at h
      apply_fun Prod.fst at h
      simp at h
