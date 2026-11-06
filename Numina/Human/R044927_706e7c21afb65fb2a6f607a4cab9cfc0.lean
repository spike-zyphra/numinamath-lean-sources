import Mathlib

open Real Finset

/- \section*{Problem 22}

What is the smallest $\mathrm{n}$ for which there is a solution to $\sin \mathrm{x}_{1}+\sin \mathrm{x}_{2}+\ldots+\sin \mathrm{x}_{\mathrm{n}}=0, \sin \mathrm{x}_{1}+$ $2 \sin \mathrm{x}_{2}+\ldots+\mathrm{n} \sin \mathrm{x}_{\mathrm{n}}=100 ?$

 -/
theorem algebra_208088 :
    IsLeast {n : ℕ | ∃ x : Fin n → ℝ, (∑ i : Fin n, sin (x i)) = 0 ∧
      (∑ i : Fin n, (i+1) * sin (x i)) = 100} 20 := by
  simp only [IsLeast, Set.mem_setOf_eq, lowerBounds, forall_exists_index, and_imp]
  constructor
  -- Show that n = 20 satisfies all requirements.
  -- Define x(i) = π / 2 + π if i < 10 and x(i) = π / 2 for 10 ≤ i < 20.
  · set x : Fin 20 → ℝ := fun i => if i < 10 then π / 2 + π else π / 2
    use x
    -- ∑ i : Fin 20, f(i) = ∑ i ∈ [0, 10), f(i) + ∑ i ∈ [0, 10), f(i + 10).
    simp_rw [sum_fin_eq_sum_range]
    rw [show range 20 = range (10 + 10) from rfl]
    simp_rw [sum_range_add]
    constructor
    -- Show that ∑ i ∈ [0, 10), sin(x(i)) + ∑ i ∈ [0, 10), sin(x(i + 10)) = 0.
    -- We have 0 = ∑ i ∈ [0, 10), (-1) + ∑ i ∈ [0, 10), 1.
    · have eq : (0 : ℝ) = ∑ i ∈ range 10, (-1) + ∑ i ∈ range 10, 1 := by simp
      nth_rw 3 [eq]
      -- It is enough to show that sin(x(i)) = -1 for i ∈ [0, 10) and
      -- sin(x(i + 10)) = 1 for i ∈ [0, 10).
      congr 1 <;> (apply sum_congr rfl; simp only [mem_range]; intro i hi)
      · simp [show i < 20 by linarith, x]
        set j : Fin 20 := ⟨i, _⟩
        have : j < 10 := by
          rw [Fin.lt_iff_val_lt_val]
          simp [show (10 : Fin 20).val = 10 from rfl, hi]
        simp [this]
      · simp [show 10 + i < 20 by linarith, x]
        set j : Fin 20 := ⟨10 + i, _⟩
        have : ¬ j < 10 := by
          rw [Fin.lt_iff_val_lt_val]
          simp [show (10 : Fin 20).val = 10 from rfl]
        simp [this]
    -- Show that ∑ i ∈ [0, 10), (i + 1) * sin(x(i)) + ∑ i ∈ [0, 10), (i + 11) * sin(x(i + 10)) = 100.
    -- We have 100 = ∑ i ∈ [0, 10), -(i + 1) + ∑ i ∈ [0, 10), (11 + i).
    · have eq : (100 : ℝ) = ∑ i ∈ range 10, -(i + 1 : ℝ) + ∑ i ∈ range 10, (11 + i : ℝ) := by norm_num
      rw [eq]
      -- It is enough to show that (i + 1) * sin(x(i)) = -(i + 1) for i ∈ [0, 10) and
      -- (i + 11) * sin(x(i + 10)) = 11 + i for i ∈ [0, 10).
      congr 1 <;> (apply sum_congr rfl; simp only [mem_range]; intro i hi)
      · simp [show i < 20 by linarith, x]
        set j : Fin 20 := ⟨i, _⟩
        have : j < 10 := by
          rw [Fin.lt_iff_val_lt_val]
          simp [show (10 : Fin 20).val = 10 from rfl, hi]
        simp [this]
      · simp [show 10 + i < 20 by linarith, x]
        set j : Fin 20 := ⟨10 + i, _⟩
        have : ¬ j < 10 := by
          rw [Fin.lt_iff_val_lt_val]
          simp [show (10 : Fin 20).val = 10 from rfl]
        simp [this]
        ring
  -- Assume now that ∑ i ∈ [0, n), sin(x(i)) = 0 and ∑ i ∈ [0, n), (i + 1) * sin(x(i)) = 100
  -- for some n and x.
  -- Show that 20 ≤ n.
  · intro n x h0 h1
    -- Assume that n < 20 and derive a contradiction.
    by_contra! hn
    -- Define y(i) = x(i) if i < n and y(i) = 0 otherwise.
    set y : ℕ → ℝ := fun i => if h : i < n then x ⟨i, h⟩ else 0
    -- Show that ∑ i ∈ [0, 19), sin(y(i)) = 0.
    replace h0 : ∑ i ∈ range 19, sin (y i) = 0 := calc
      -- We have ∑ i ∈ [0, 19), sin(y(i)) = ∑ i ∈ [0, n), sin(y(i)) + 0.
      ∑ i ∈ range 19, sin (y i) = ∑ i ∈ range n, sin (y i) + 0 := by
          rw [show 19 = n + (19 - n) by omega]
          rw [sum_range_add]
          congr
          apply sum_eq_zero
          intro i hi
          simp [y]
      -- ∑ i ∈ [0, n), sin(y(i)) = ∑ i ∈ [0, n), sin(x(i)) = 0.
      _ = ∑ i : Fin n, sin (x i) := by
          rw [sum_fin_eq_sum_range, add_zero]
          apply sum_congr rfl
          intro i hi
          simp only [mem_range] at hi
          simp [y, hi]
      _ = 0 := by rw [h0]
    -- Show that ∑ i ∈ [0, 19), (i + 1) * sin(y(i)) = 100.
    replace h1 : ∑ i ∈ range 19, (i + 1) * sin (y i) = 100 := calc
      -- We have ∑ i ∈ [0, 19), (i + 1) * sin(y(i)) = ∑ i ∈ [0, n), (i + 1) * sin(y(i)) + 0.
      ∑ i ∈ range 19, (i + 1) * sin (y i) = ∑ i ∈ range n, (i + 1) * sin (y i) + 0 := by
          rw [show 19 = n + (19 - n) by omega]
          rw [sum_range_add]
          congr
          apply sum_eq_zero
          intro i hi
          simp [y]
      -- ∑ i ∈ [0, n), (i + 1) * sin(y(i)) = ∑ i ∈ [0, n), (i + 1) * sin(x(i)) = 100.
      _ = ∑ i : Fin n, (i + 1) * sin (x i) := by
          rw [sum_fin_eq_sum_range, add_zero]
          apply sum_congr rfl
          intro i hi
          simp only [mem_range] at hi
          simp [y, hi]
      _ = 100 := by rw [h1]
    -- Show that ∑ i ∈ [0, 19), (i + 1) * sin(y(i)) < 100.
    contrapose! h1
    apply ne_of_lt
    calc
      -- We have ∑ i ∈ [0, 19), (i + 1) * sin(y(i))
      --   = ∑ i ∈ [0, 19), (i + 1) * sin(y(i)) - ∑ i ∈ [0, 19), 10 * sin(y(i))
      --   = ∑ i ∈ [0, 10), (i - 9) * sin(y(i)) + ∑ i ∈ [0, 9), (i + 1) * sin(y(i))
      --   ≤ ∑ i ∈ [0, 10), (9 - i) + ∑ i ∈ [0, 9), (i + 1) (because -1 ≤ sin y ≤ 1)
      --   = 90 < 100.
      ∑ i ∈ range 19, (i + 1) * sin (y i) = ∑ i ∈ range 19, (i + 1) * sin (y i) - ∑ i ∈ range 19, 10 * sin (y i) := by
          rw [← mul_sum, h0, mul_zero, sub_zero]
      _ = ∑ i ∈ range 10, (i - 9) * sin (y i) + ∑ i ∈ range 9, (i + 1) * sin (y (i + 10)) := by
          rw [← sum_sub_distrib, show 19 = 10 + 9 by norm_num, sum_range_add]
          congr <;> (ext i; push_cast; ring_nf)
      _ ≤ ∑ i ∈ range 10, (9 - i : ℝ) + ∑ i ∈ range 9, (i + 1 : ℝ) := by
          gcongr with i hi i hi <;> simp only [mem_range] at hi
          · suffices 0 ≤ (9 - i : ℝ) * (1 + sin (y i)) by linear_combination this
            apply mul_nonneg
            · suffices (i : ℝ) ≤ 9 by linarith
              norm_cast
              omega
            · linarith [Real.neg_one_le_sin (y i)]
          · suffices 0 ≤ (i + 1) * (1 - sin (y (i + 10))) by linear_combination this
            apply mul_nonneg
            · linarith
            · linarith [Real.sin_le_one (y (i + 10))]
      _ = 90 := by norm_num
      _ < 100 := by norm_num