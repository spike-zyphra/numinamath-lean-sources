import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Irrational

open Real

/-- For how many [ordered pairs](https://artofproblemsolving.com/wiki/index.php/Ordered_pair)
$(x,y)$ of [integers](https://artofproblemsolving.com/wiki/index.php/Integer) is it true that
$0 < x < y < 10^6$ and that the
[arithmetic mean](https://artofproblemsolving.com/wiki/index.php/Arithmetic_mean) of $x$ and $y$ is
exactly $2$ more than the
[geometric mean](https://artofproblemsolving.com/wiki/index.php/Geometric_mean) of $x$ and $y$? -/
theorem algebra_714 :
    {(x , y) : ℕ × ℕ | 0 < x ∧ x < y ∧ y < 10^6 ∧
    (x + y) / 2 = 2 + √(x*y)}.ncard = 997 := by

  have {x y : ℝ} (xpos : 0 < x) (xlty : x < y) : √(x) < √(y) := by
    rw [sqrt_lt_sqrt_iff (by linarith)]; assumption

  have aux₁ {x y : ℝ} (xpos : 0 < x) (xlty : x < y) : 0 < √(y) - √(x) := by
    rw [sub_pos]; exact this xpos xlty

  -- This is the square of addition formula for $\sqrt{x}$ and $\sqrt{y}$.
  have aux₂ {x y : ℝ} (xpos : 0 < x) (xlty : x < y) : (√(y) - √(x))^2 = x + y - 2*√(x*y) := by
    calc _ = (√(x))^2 + (√(y))^2 - 2*√(x)*√(y) := by ring
         _ = _ := by rw [sq_sqrt, sq_sqrt, sqrt_mul, mul_assoc] <;> linarith

  -- Using this formula, we can rewrite the equation in the problem. We discard the solution
  -- corresponding to $-2$ because $x < y$ and hence $\sqrt{x} < \sqrt{y}$.
  have h₁ {x y : ℝ} (xpos : 0 < x) (xlty : x < y) :
      (x + y) / 2 = 2 + √(x * y) ↔ √(y) = √(x) + 2 := by
    constructor <;> intro h
    · calc √(y) = √(y) - √(x) + √(x) := by ring
           _ = √((√(y) - √(x))^2) + √(x) := by rw [sqrt_sq]; linarith [aux₁ xpos xlty]
           _ = √(x + y - 2 * √(x * y)) + √(x) := by rw [aux₂ xpos xlty]
           _ = √(2 * ((x + y) / 2) - 2 * √(x * y)) + √(x) := by simp [mul_div_cancel₀]
           _ = √(2 * (2 + √(x * y)) - 2 * √(x * y)) + √(x) := by rw [h]
           _ = √(2^2) + √(x) := by ring_nf
           _ = √(x) + 2 := by simp [add_comm]
    · calc (x + y) / 2 = ((x + y) - 2 * √(x * y)) / 2 + √(x * y) := by ring
           _ = (√(y) - √(x))^2 / 2 + √(x * y) := by rw [aux₂ xpos xlty]
           _ = (√(x) + 2 - √(x))^2 / 2 + √(x * y) := by rw [h]
           _ = 2 + √(x * y) := by ring

  -- The problem is about natural numbers, so we prove the same result for natural numbers.
  have h₂ {x y : ℕ} (xpos : 0 < x) (xlty : x < y) :
      (x + y) / 2 = 2 + √(x * y) ↔ √(y) = √(x) + 2 := by
    apply h₁ (by simp [xpos]) (by simp [xlty])

  -- We prove that if $\sqrt{y} = \sqrt{x} + 2$, then $x = a^2$ and $y = (a + 2)^2$ for some $a$.
  have h₃ {x y : ℕ} (h : √(y) = √(x) + 2) : ∃ a, x = a^2 ∧ y = (a + 2)^2 := by

    -- First, we solve for $\sqrt{x}$ in terms of $x$ and $y$.
    have : √(x) = (y - x - (4 : ℕ)) / (4 : ℕ) := by
      calc _ = (4 * √(x)) / 4 := by ring
           _ = (4 * √(x) + (√(x)^2) + 4 - x - 4) / 4 := by rw [sq_sqrt (by linarith)]; ring
           _ = ((√(x) + 2)^2 - x - 4) / 4 := by ring
           _ = ((√(y))^2 - x - 4) / 4 := by rw [h]
           _ = (y - x - 4) / 4 := by rw [sq_sqrt (by linarith)]

    -- We see that $\sqrt{x}$ is rational.
    have : ¬ Irrational (√(x)) := by
      by_contra! h'
      rw [this] at h'
      replace h' := Irrational.of_div_nat 4 h'
      revert h'; simp only [imp_false]
      convert Int.not_irrational ((y : ℤ) - x - 4)
      norm_cast

    -- Because $\sqrt{x}$ is rational, $x$ must be a perfect square.
    have : IsSquare x := by
      by_contra h'
      rw [←irrational_sqrt_natCast_iff] at h'
      contradiction

    -- Let $a$ be the square root of $x$ which is a natural number.
    rcases (isSquare_iff_exists_sq x).mp this with ⟨a, ha⟩
    use a, ha

    suffices (y : ℝ) = (a + 2)^2 from (by norm_cast at this)

    -- We substitute $a^2$ for $x$ in the equation $\sqrt{y} = \sqrt{x} + 2$ and solve for $y$.
    calc y = (√(y))^2 := by rw [sq_sqrt (by linarith)]
         _ = (√(x) + 2)^2 := by rw [h]
         _ = (√(a^2) + 2)^2 := by simp [ha]
         _ = (a + 2)^2 := by rw [sqrt_sq (by linarith)]

  -- Using these results, we simplify our condition.
  have h₄ {x y : ℕ} : (0 < x ∧ x < y ∧ y < 10^6 ∧ (x + y) / 2 = 2 + √(x * y)) ↔
      (∃ a, (0 < a ∧ a < 998) ∧ x = a^2 ∧ y = (a + 2)^2) := by
    constructor
    · rintro ⟨xpos, xlty, ylt, h⟩
      rw [h₁] at h
      replace h := h₃ h
      rcases h with ⟨a, hxa, hya⟩
      use a
      exact ⟨⟨by nlinarith, by nlinarith⟩, by exact hxa, by exact hya⟩
      · simp [xpos]
      · simp [xlty]
    · rintro ⟨a, ⟨apos, alt⟩, hxa, hya⟩
      refine ⟨by nlinarith, by nlinarith, by nlinarith, ?_⟩
      rw [hxa, hya, sqrt_mul (by linarith)]
      push_cast
      rw [sqrt_sq (by linarith), sqrt_sq (by linarith)]
      ring

  have {a : ℕ} : (0 < a ∧ a < 998) ↔ (a ∈ Set.Icc 1 997) := by
    simp
    constructor <;> intro <;> constructor <;> linarith

  simp_rw [h₄, this]

  -- To count the number of solutions, we find a bijection between the set of solutions and
  -- the set $\{1, 2, \ldots, 997\}$.
  let g : (a : ℕ) → (a ∈ Set.Icc 1 997) → ℕ × ℕ :=
    fun a _ => (a^2, (a + 2)^2)

  symm
  trans
  · show 997 = (Set.Icc 1 997).ncard
    simp [←Set.Nat.card_coe_set_eq]
  · apply Set.ncard_congr g
    -- $g$ really is function into the set of solutions.
    · intro a ha
      simp [←Set.Nat.card_coe_set_eq]
      exact ha
    -- $g$ is injective.
    · intro a b ha hb hab
      aesop
    -- $g$ is surjective.
    · rintro ⟨x, y⟩ ⟨a, ha, rfl, rfl⟩
      use a, ha