import Mathlib

def rationalSolutions :=
  {s : ℚ × ℚ × ℚ | ∃ x y z : ℚ, s = (x, y, z) ∧ x ≠ 1 ∧ y ≠ 1 ∧ z ≠ 1 ∧ x * y * z = 1 ∧
    x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 = 1}

/-(a) Prove the inequality  $$ \frac{x^{2}}{(x-1)^{2}}+\frac{y^{2}}{(y-1)^{2}}+\frac{z^{2}}{(z-1)^{2}} \geq 1 $$  for real numbers $x, y, z \neq 1$ satisfying the condition $x y z=1$.  (b) Show that there are infinitely many triples of rational numbers $x, y, z$ for which this inequality turns into equality.-/
theorem algebra_23719 (x y z : ℝ) (h : x * y * z = 1) (hx : x ≠ 1) (hy : y ≠ 1) (hz : z ≠ 1) :
    x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 ≥ 1 ∧
    Set.Infinite rationalSolutions := by
  constructor
  · -- Since $xyz = 1$, we can apply the substitution $x = \frac{a}{b}, y = \frac{b}{c}, z = \frac{c}{a}$.
    have h1 : ∃ a b c : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ x = a / b ∧ y = b / c ∧ z = c / a := by
      use x, 1, 1 / y
      obtain ⟨⟨hx, hy⟩, _⟩ : (x ≠ 0 ∧ y ≠ 0) ∧ z ≠ 0 := by
        have := h.symm ▸ one_ne_zero
        simpa [not_or] using this
      have : z * (y * x) = 1 := by rw [← h]; ac_rfl
      field_simp [*]
    obtain ⟨a, b, c, ha, hb, hc, rfl, rfl, rfl⟩ := h1
    --Then we define $m = c-b, n = b-a$ and rewrite the inequality as LHS - 1 $\geq 0$
    obtain ⟨m, n, rfl, rfl⟩ : ∃ m n, b = c - m ∧ a = c - m - n := by use c - b, b - a; simp
    have hm_ne_zero : m ≠ 0 := by contrapose! hy; field_simp; assumption
    have hn_ne_zero : n ≠ 0 := by contrapose! hx; field_simp; assumption
    have hmn_ne_zero : m + n ≠ 0 := by contrapose! hz; field_simp; linarith
    have hc_sub_sub : c - (c - m - n) = m + n := by abel
    rw [ge_iff_le, ← sub_nonneg]
    -- using $c, m$ and $n$. We factor LHS - 1 as a square, which finishes the proof.
    convert sq_nonneg ((c * (m ^ 2 + n ^ 2 + m * n) - m * (m + n) ^ 2) / (m * n * (m + n)))
    field_simp [hc_sub_sub]; ring
  · -- We present a set $W$ of rational triples.
    let W := {s : ℚ × ℚ × ℚ | ∃ x y z : ℚ, s = (x, y, z) ∧
      ∃ t : ℚ, t > 0 ∧ x = -(t + 1) / t ^ 2 ∧ y = t / (t + 1) ^ 2 ∧ z = -t * (t + 1)}
    -- We prove that $W$ is a subset of the set of rational solutions to the equation
    have hW_sub_S : W ⊆ rationalSolutions := by
      intro s hs_in_W
      rw [rationalSolutions]
      simp only [Set.mem_setOf_eq] at hs_in_W ⊢
      rcases hs_in_W with ⟨x, y, z, h₁, t, ht_gt_zero, hx_t, hy_t, hz_t⟩
      use x, y, z
      have key_gt_zero : t ^ 2 + t + 1 > 0 := by linarith [pow_pos ht_gt_zero 2, ht_gt_zero]
      have h₂ : x ≠ 1 := by rw [hx_t]; field_simp; linarith [key_gt_zero]
      have h₃ : y ≠ 1 := by rw [hy_t]; field_simp; linarith [key_gt_zero]
      have h₄ : z ≠ 1 := by rw [hz_t]; linarith [key_gt_zero]
      have h₅ : x * y * z = 1 := by rw [hx_t, hy_t, hz_t]; field_simp; ring
      have h₆ : x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 = 1 := by
        have hx1 : (x - 1) ^ 2 = (t ^ 2 + t + 1) ^ 2 / t ^ 4 := by
          field_simp; rw [hx_t]; field_simp; ring
        have hy1 : (y - 1) ^ 2 = (t ^ 2 + t + 1) ^ 2 / (t + 1) ^ 4 := by
          field_simp; rw [hy_t]; field_simp; ring
        have hz1 : (z - 1) ^ 2 = (t ^ 2 + t + 1) ^ 2 := by rw [hz_t]; ring
        calc
          x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 =
              (x ^ 2 * t ^ 4 + y ^ 2 * (t + 1) ^ 4 + z ^ 2) / (t ^ 2 + t + 1) ^ 2 := by
            rw [hx1, hy1, hz1]; field_simp
          _ = 1 := by rw [hx_t, hy_t, hz_t]; field_simp; ring
      exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
    -- and that $W$ is infinite.
    have hW_inf : Set.Infinite W := by
      let g : ℚ × ℚ × ℚ → ℚ := fun s => -s.2.2
      let K := g '' W
      have hK_not_bdd : ¬BddAbove K := by
        rw [not_bddAbove_iff]
        intro q
        let t : ℚ := max (q + 1) 1
        use t * (t + 1)
        have h₁ : t * (t + 1) ∈ K := by
          let x : ℚ := -(t + 1) / t ^ 2
          let y : ℚ := t / (t + 1) ^ 2
          set z : ℚ := -t * (t + 1) with hz_def
          simp only [t, W, K, g, Set.mem_image, Prod.exists]
          use x, y, z; constructor
          · simp only [Set.mem_setOf_eq]
            use x, y, z; constructor
            · rfl
            · use t; constructor
              · simp only [t, gt_iff_lt, lt_max_iff]; right; trivial
              exact ⟨rfl, rfl, rfl⟩
          · have hg : -z = g (x, y, z) := rfl
            rw [hg, hz_def]; ring
        have h₂ : q < t * (t + 1) := by linarith [sq_nonneg t, le_max_left (q + 1) 1]
        exact ⟨h₁, h₂⟩
      have hK_inf : Set.Infinite K := by intro h; apply hK_not_bdd; exact Set.Finite.bddAbove h
      exact hK_inf.of_image g
    -- We conclude that there are infinitely many triples of rational numbers $x, y, z$ for which this inequality turns into equality.
    exact hW_inf.mono hW_sub_S