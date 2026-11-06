import Mathlib

/- Six paniers à fruits contiennent des poires, des pêches et des pommes.
   Le nombre de pêches dans chaque panier est égal au nombre total de pommes dans les autres paniers.
   Le nombre de pommes dans chaque panier est égal au nombre total de poires dans les autres paniers.
   Montrez que le nombre total de fruits est un multiple de 31. -/

-- Define the quantities of pears, apples, and peaches in 6 baskets
theorem number_theory_607388
  (p₁ p₂ p₃ p₄ p₅ p₆ : ℕ) -- Quantity of pears in each basket
  (q₁ q₂ q₃ q₄ q₅ q₆ : ℕ) -- Quantity of apples in each basket
  (r₁ r₂ r₃ r₄ r₅ r₆ : ℕ) -- Quantity of peaches in each basket
  -- Condition 1: In each basket, the number of apples equals the total pears in other baskets
  (hq₁ : q₁ = p₂ + p₃ + p₄ + p₅ + p₆)
  (hq₂ : q₂ = p₁ + p₃ + p₄ + p₅ + p₆)
  (hq₃ : q₃ = p₁ + p₂ + p₄ + p₅ + p₆)
  (hq₄ : q₄ = p₁ + p₂ + p₃ + p₅ + p₆)
  (hq₅ : q₅ = p₁ + p₂ + p₃ + p₄ + p₆)
  (hq₆ : q₆ = p₁ + p₂ + p₃ + p₄ + p₅)
  -- Condition 2: In each basket, the number of peaches equals the total apples in other baskets
  (hr₁ : r₁ = q₂ + q₃ + q₄ + q₅ + q₆)
  (hr₂ : r₂ = q₁ + q₃ + q₄ + q₅ + q₆)
  (hr₃ : r₃ = q₁ + q₂ + q₄ + q₅ + q₆)
  (hr₄ : r₄ = q₁ + q₂ + q₃ + q₅ + q₆)
  (hr₅ : r₅ = q₁ + q₂ + q₃ + q₄ + q₆)
  (hr₆ : r₆ = q₁ + q₂ + q₃ + q₄ + q₅) :
  31 ∣ (p₁ + p₂ + p₃ + p₄ + p₅ + p₆ + q₁ + q₂ + q₃ + q₄ + q₅ + q₆ + r₁ + r₂ + r₃ + r₄ + r₅ + r₆) := by
  -- Define total quantities
  let P := p₁ + p₂ + p₃ + p₄ + p₅ + p₆  -- Total number of pears
  let Q := q₁ + q₂ + q₃ + q₄ + q₅ + q₆  -- Total number of apples
  let R := r₁ + r₂ + r₃ + r₄ + r₅ + r₆  -- Total number of peaches
  let T := P + Q + R                     -- Total number of fruits

  -- Step 1: Prove that Q = 5 * P
  have hQ : Q = 5 * P := by
    calc Q
      = q₁ + q₂ + q₃ + q₄ + q₅ + q₆ := rfl
    _ = (p₂ + p₃ + p₄ + p₅ + p₆) + (p₁ + p₃ + p₄ + p₅ + p₆) + (p₁ + p₂ + p₄ + p₅ + p₆) +
        (p₁ + p₂ + p₃ + p₅ + p₆) + (p₁ + p₂ + p₃ + p₄ + p₆) + (p₁ + p₂ + p₃ + p₄ + p₅) := by rw [hq₁, hq₂, hq₃, hq₄, hq₅, hq₆]
    _ = 5 * p₁ + 5 * p₂ + 5 * p₃ + 5 * p₄ + 5 * p₅ + 5 * p₆ := by
      ring_nf  -- Simplify the expression, each pear appears exactly 5 times
    _ = 5 * (p₁ + p₂ + p₃ + p₄ + p₅ + p₆) := by rw [← mul_add, ← mul_add, ← mul_add, ← mul_add, ← mul_add]
    _ = 5 * P := rfl

  -- Step 2: Prove that R = 5 * Q
  have hR : R = 5 * Q := by
    calc R
      = r₁ + r₂ + r₃ + r₄ + r₅ + r₆ := rfl
    _ = (q₂ + q₃ + q₄ + q₅ + q₆) + (q₁ + q₃ + q₄ + q₅ + q₆) + (q₁ + q₂ + q₄ + q₅ + q₆) +
        (q₁ + q₂ + q₃ + q₅ + q₆) + (q₁ + q₂ + q₃ + q₄ + q₆) + (q₁ + q₂ + q₃ + q₄ + q₅) := by rw [hr₁, hr₂, hr₃, hr₄, hr₅, hr₆]
    _ = 5 * q₁ + 5 * q₂ + 5 * q₃ + 5 * q₄ + 5 * q₅ + 5 * q₆ := by
      ring_nf  -- Simplify the expression, each apple appears exactly 5 times
    _ = 5 * (q₁ + q₂ + q₃ + q₄ + q₅ + q₆) := by rw [← mul_add, ← mul_add, ← mul_add, ← mul_add, ← mul_add]
    _ = 5 * Q := rfl

  -- Step 3: Calculate T = 31 * P
  have hT : T = 31 * P := by
    calc T
      = P + Q + R := rfl
    _ = P + 5 * P + 5 * Q := by
      rw [hQ]  -- Substitute Q with 5 * P
      rw[hR]
      rw[hQ]
    _ = P + 5 * P + 5 * (5 * P) := by rw [hQ]
    _ = P + 5 * P + 25 * P := by
      ring_nf  -- Simplify the expression
    _ = (1 + 5 + 25) * P := by ring
    _ = 31 * P := rfl

  have h31 : 31 ∣ T := by
    use P  -- There exists a natural number P such that T = 31 * P
  -- Conclusion: T is a multiple of 31
  unfold T at h31
  unfold P Q R at h31
  simp[←add_assoc]at h31
  exact h31