import Mathlib

/- 12. (POL 1) If $a$ and $b$ are arbitrary positive real numbers and $m$ an integer, prove that  $$ \left(1+\frac{a}{b}\right)^{m}+\left(1+\frac{b}{a}\right)^{m} \geq 2^{m+1} $$ -/
theorem inequalities_24770
    (a b : ℝ)
    (m : ℤ)
    (h₀ : 0 < a)
    (h₁ : 0 < b)
: (1 + a / b) ^ m + (1 + b / a) ^ m ≥ 2 ^ (m + 1) := by
    -- The given in equality is equivalent to (1 + a / b) ^ m + (1 + b / a) ^ m ≥ 2 ^ (m + 1)
    rw [show 1 + a / b = (a + b) / b by field_simp; ring, div_zpow]
    rw [show 1 + b / a = (a + b) / a by field_simp, div_zpow]


    -- We can rewrite this as [h]
    suffices h : (1 / a^m + 1 / b^m) / 2 ≥ (2 / (a + b))^m by
        apply_fun (fun x : ℝ  => 2*x) at h
        dsimp at h
        rw [show  2 * ((1 / a ^ m + 1 / b ^ m) / 2) = ((1 / a ^ m + 1 / b ^ m)) by field_simp; ring] at h
        apply_fun (fun x : ℝ  => x*(a+b)^m) at h
        dsimp at h
        rw [show (2 / (a + b)) ^ m = 2^m / (a + b)^m by field_simp] at h
        rw [show 2 * (2 ^ m / (a + b) ^ m) * (a + b) ^ m = 2 * ((2 ^ m / (a + b) ^ m) * (a + b) ^ m) by ac_rfl] at h
        rw [show (2 ^ m / (a + b) ^ m * (a + b) ^ m) = 2 ^ m by field_simp] at h
        have : (2: ℝ) * 2 ^ m = 2 ^ ((m: ℝ) + 1) := by
            rw [Real.rpow_add, Real.rpow_intCast, Real.rpow_one]
            ac_rfl
            norm_num
        norm_cast at this
        rw [this] at h
        have : (1 / a ^ m + 1 / b ^ m) * (a + b) ^ m = (a + b) ^ m / a ^ m + (a + b) ^ m / b ^ m := by
            field_simp
            ring
        rw [this] at h
        linarith
        apply Monotone.mul_const
        exact fun ⦃a b⦄ a => a
        positivity
        apply Monotone.const_mul
        exact fun ⦃a b⦄ a => a
        norm_num

    -- The function x ^ (-m) is convex on (0, ∞)
    have hc : ConvexOn ℝ (Set.Ioi (0: ℝ)) fun x => x ^ (-m) := by
        apply convexOn_zpow

    -- Define the weights and points for Jensen's inequality. We will use the points {a, b} each with weight 1/2
    let w : Fin 2 → ℝ := fun _ => (1:ℝ)/2

    let p : Fin 2 → ℝ := fun i =>
        match i with
        | 0 => a
        | 1 => b

    let s : Finset (Fin 2) := Finset.univ

    have hw : ∀ i ∈ s, 0 ≤ w i := by
        intro i hi
        fin_cases i <;> positivity

    have hw' : ∑ i ∈ s, w i = 1 := by
        rw [Fin.sum_univ_two]
        unfold w
        norm_num

    have hmem : ∀ i ∈ s, p i ∈ Set.Ioi (0 : ℝ) := by
        intro i hi
        fin_cases i
        simp
        rw [show p 0 = a by rfl]
        positivity
        rw [show p 1 = b by rfl]
        simp
        positivity

    -- Jensen's inequality: (f(a) + f(b)) / 2 ≥ f((a + b) / 2)
    have jensens := hc.map_sum_le hw hw' hmem

    simp at jensens
    rw [Fin.sum_univ_two] at jensens
    rw [Fin.sum_univ_two] at jensens

    unfold w at jensens

    rw [show p 0 = a by rfl, show p 1 = b by rfl] at jensens

    clear hmem
    clear p

    -- This is now equivalent to the goal, but we need to clean up

    rw [show (1 / 2 * a + 1 / 2 * b) = (a + b) / 2 by field_simp] at jensens

    have : (((a + b) / 2) ^ m)⁻¹ = (2 / (a + b)) ^ m := by
        rw [←inv_zpow]
        congr
        rw [inv_div]

    rw [this] at jensens
    simp
    linarith
