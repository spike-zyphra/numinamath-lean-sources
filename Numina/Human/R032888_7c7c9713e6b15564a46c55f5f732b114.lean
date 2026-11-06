import Mathlib

/- Let $\mathbb{R}_{>0}$ be the set of positive real numbers. Determine all functions $f: \mathbb{R}_{>0} \rightarrow \mathbb{R}_{>0}$ such that  $$ x(f(x)+f(y)) \geqslant(f(f(x))+y) f(y) $$  for every $x, y \in \mathbb{R}_{>0}$. (Belgium) Answer: All functions $f(x)=\frac{c}{x}$ for some $c>0$. -/
theorem algebra_607765 :
    {f : {x : ℝ // 0 < x} → {x : ℝ // 0 < x} | ∀ x y, x * (f x + f y) ≥ (f (f x) + y) * f y} = {fun ⟨x, hx⟩ => ⟨c / x, div_pos hc hx⟩ | (c : ℝ) (hc : c > 0)} := by
  ext f
  constructor
  . simp
    intro h
    -- Lemma 1: x ≥ f^[2](x)
    -- By setting y = x in the given inequality
    have h₁ (x : ℝ) (hx : 0 < x) : x ≥ f^[2] ⟨x, hx⟩ := by
      specialize h x hx x hx
      simp [← Subtype.coe_le_coe] at h
      simp
      nlinarith [(f ⟨x, hx⟩).property]
    -- Lemma 2: f(y) - f^[3](y) ≥ y - f^[2](y)
    -- By setting x = f(y) in the given inequality
    have h₂ (y : ℝ) (hy : 0 < y) : f ⟨y, hy⟩ - f^[3] ⟨y, hy⟩ ≥ y - f^[2] ⟨y, hy⟩ := by
      specialize h (f ⟨y, hy⟩).val (f ⟨y, hy⟩).property y hy
      simp [← Subtype.coe_le_coe] at h
      simp
      nlinarith [(f ⟨y, hy⟩).property]
    -- Lemma 3: f^[n+1](y) - f^[n+3](y) ≥ f^[n](y) - f^[n+2](y)
    -- By setting y = f^[n](y) in lemma 2
    have h₃ (y : ℝ) (hy : 0 < y) (n : ℕ) : (f^[n+1] ⟨y, hy⟩ - f^[n+3] ⟨y, hy⟩ : ℝ) ≥ f^[n] ⟨y, hy⟩ - f^[n+2] ⟨y, hy⟩ := by
      -- Compare the goal with lemma 2 when y := f^[n](y)
      convert h₂ (f^[n] ⟨y, hy⟩).val (f^[n] ⟨y, hy⟩).property using 2
      all_goals
        simp [-Function.iterate_succ]
        rw [← Subtype.eq_iff, add_comm]
        apply Function.iterate_add_apply
    -- Lemma 4: f^[n](y) - f^[n+2](y) ≥ y - f^[2](y)
    -- By applying lemma 3 many times
    have h₄ (y : ℝ) (hy : 0 < y) (n : ℕ) : f^[n] ⟨y, hy⟩ - f^[n+2] ⟨y, hy⟩ ≥ y - f^[2] ⟨y, hy⟩ := by
      -- Simple induction
      induction n with
      | zero => simp
      | succ n ih => exact ih.trans (h₃ y hy n)
    -- Lemma 5: y - f^[2*m](y) ≥ m * (y - f^[2](y))
    -- By applying lemma 4 many times and adding the inequalities
    have h₅ (y : ℝ) (hy : 0 < y) (m : ℕ) : y - f^[2*m] ⟨y, hy⟩ ≥ m * (y - f^[2] ⟨y, hy⟩) := by
      -- Simple induction
      induction m with
      | zero => simp
      | succ m ih =>
        calc y - f^[2 * (m + 1)] ⟨y, hy⟩
          _ = y - f^[2 * m + 2] ⟨y, hy⟩ := by rw [Nat.mul_succ]
          _ = (y - f^[2 * m] ⟨y, hy⟩) + (f^[2 * m] ⟨y, hy⟩ - f^[2 * m + 2] ⟨y, hy⟩) := by ring
          _ ≥ m * (y - f^[2] ⟨y, hy⟩) + (y - f^[2] ⟨y, hy⟩) := add_le_add ih (h₄ y hy (2 * m)) -- Use the induction hypothesis
          _ = ↑(m + 1 : ℕ) * (y - f^[2] ⟨y, hy⟩) := by rify; ring
    -- Lemma 6: f^[2](y) = y
    have h₆ (y : ℝ) (hy : 0 < y) : f^[2] ⟨y, hy⟩ = y := by
      -- If otherwise, we have y - f^[2](y) > 0
      refine (LE.le.not_lt_iff_eq (h₁ y hy)).mp fun H => ?_
      rw [← sub_pos] at H
      -- By setting m to be large enough, we have m * (y - f^[2](y)) ≥ y
      obtain ⟨m, hm⟩ := Archimedean.arch y H
      rw [nsmul_eq_mul] at hm
      -- So it contradicts the lemma 5
      linarith only [hm, h₅ y hy m, (f^[2 * m] ⟨y, hy⟩).property]
    -- Lemma 7: x * f(x) ≥ y * f(y)
    -- By simplifying the original inequality using lemma 6
    have h₇ (x : ℝ) (hx : 0 < x) (y : ℝ) (hy : 0 < y) : x * f ⟨x, hx⟩ ≥ y * f ⟨y, hy⟩ := by
      specialize h x hx y hy
      specialize h₆ x hx
      simp at h₆ ⊢
      simp [← Subtype.coe_le_coe, h₆] at h
      linarith only [h]
    -- So x * f(x) is a constant, so we have f(x) = f(1) / x
    use f ⟨1, one_pos⟩, (f ⟨1, one_pos⟩).property
    ext ⟨x, hx⟩
    simp
    have h₈ := (h₇ 1 one_pos x hx).antisymm (h₇ x hx 1 one_pos)
    field_simp
    linarith only [h₈]
  . -- Conversely, if f(x) = c / x, then it is easy to verify that it satisfies the given inequality
    rintro ⟨c, hc, rfl⟩
    intro ⟨x, hx⟩ ⟨y, hy⟩
    refine le_of_eq (Subtype.eq ?_)
    field_simp
    ring
