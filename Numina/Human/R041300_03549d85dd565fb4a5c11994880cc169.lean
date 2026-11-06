import Mathlib

/- Voor reële getallen $x$ en $y$ definiëren we $M(x, y)$ als het maximum van de drie getallen $x y,(x-1)(y-1)$ en $x+y-2 x y$. Bepaal de kleinst mogelijke waarde van $M(x, y)$ over alle reële getallen $x$ en $y$ met $0 \leq x, y \leq 1$. -/
theorem algebra_605307 :
  IsLeast {t : ℝ | ∃ x y : ℝ, x ∈ Set.Icc 0 1 ∧ y ∈ Set.Icc 0 1 ∧ t = max (max (x * y) ((x - 1) * (y - 1))) (x + y - 2 * x * y)} (4 / 9) := by
    unfold IsLeast lowerBounds
    simp
    constructor
    -- take x = 1/3, y = 1/3 to show that 4/9 can be achieved
    . use 2 / 3
      norm_num
      use 2 / 3
      norm_num

    . -- prove that the max value is equal between $(x, y)$ and $(1 - x, 1 - y)$, so we can assume $x + y \geq 1$
      have (h: ∀ x y: ℝ, x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 → 1 ≤ x + y → (4 / 9) ≤ x * y ⊔ (x - 1) * (y - 1) ⊔ (x + y - 2 * x * y) ) :
        ∀ ⦃a : ℝ⦄ (x : ℝ), 0 ≤ x → x ≤ 1 → ∀ (y : ℝ), 0 ≤ y → y ≤ 1 → a = x * y ⊔ (x - 1) * (y - 1) ⊔ (x + y - 2 * x * y) → 4 / 9 ≤ a := by
        intro t x hx_min hx_max y hy_min hy_max ht
        rw [ht]
        by_cases hx_add_y : 1 ≤ x + y
        exact h x y ⟨hx_min, hx_max⟩ ⟨hy_min, hy_max⟩ hx_add_y
        simp at hx_add_y
        -- if x + y < 1, then we can set $x = 1 - x'$, $y = 1 - y'$, so $x * y = (1 - x') * (1 - y')$, $(1 - x') * (1 - y') = xy$, $x + y - 2 * x * y = x' + y' - 2 * x' * y'$
        have := h (1 - x) (1 - y) ⟨by linarith only [hx_max], by linarith only [hx_min]⟩ ⟨by linarith only [hy_max], by linarith only [hy_min]⟩ (by linarith only [hx_add_y])
        ring_nf at this
        ring_nf
        nth_rw 2 [max_comm] at this
        exact this
      apply this
      -- now we have $x + y \geq 1$
      intro x y hx hy hx_add_y
      -- so let $t = x + y - 1$
      let t := x + y - 1
      have t_min : 0 ≤ t := by simp only [t]; linarith only [hx_add_y]
      have t_max : t ≤ 1 := by simp only [t]; linarith only [hx.2, hy.2]
      -- in this case, x * y always greater than or equal to $(x - 1) * (y - 1)$
      have : x * y ⊔ (x - 1) * (y - 1) = x * y := by
        simp
        apply le_of_sub_nonpos
        ring_nf
        rw [show 1 + (-x - y) = -t by ring_nf]
        linarith only [t_min]
      rw [this]
      -- we only to compare $x * y$ and $(x + y - 2 * x * y)$
      -- we consider two cases: $x + y \leq 1/3$ and $x + y \geq 1/3$
      by_cases x_add_y: t ≤ 1 / 3
      -- if $t ≤ 1 / 3$, using AM-GM, we have $x + y - 2 * x * y \geq 4 / 9$
      . simp
        right
        have := neg_le_neg <| four_mul_le_sq_add x y
        have (h: 4 / 9 ≤ (1 - t ^ 2)/2): 4 / 9 ≤ x + y - 2 * x * y := by
          linear_combination h + this / 2
        apply this
        have := neg_le_neg <| sq_le_sq' (by apply le_trans' t_min; norm_num) x_add_y
        linear_combination this / 2
      -- if $t \geq 1 / 3$, we have $3 * (x * y ⊔ (x + y - 2 * x * y)) ≥ x * y + x * y + x + y - 2 * x * y = x + y > 4 / 3 $
      . simp at x_add_y
        have right_min : 4 / 3 - 2 * x * y < x + y - 2 * x * y := by linarith only [x_add_y]
        have h1: x * y <= x * y ⊔ (x + y - 2 * x * y) := le_sup_left
        have h2: x + y - 2 * x * y <= x * y ⊔ (x + y - 2 * x * y) := le_sup_right
        linear_combination (h1 + h1 + h2 + x_add_y) / 3
