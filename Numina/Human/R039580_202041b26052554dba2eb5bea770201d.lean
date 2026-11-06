import Mathlib
/- 1. Find all real solutions of the system of equations


$$

\frac{1}{x+y}+z=1, \quad \frac{1}{y+z}+x=1, \quad \frac{1}{z+x}+y=1

$$
 -/
theorem algebra_267141 {x y z : ℝ}
    (h₀ : x ≠ -y) (h₁ : y ≠ -z) (h₂ : z ≠ -x)
    (h₃ : 1 / (x + y) + z = 1) (h₄ : 1 / (y + z) + x = 1) (h₅ : 1 / (z + x) + y = 1) :
    (x, y, z) = (-1, -1, 3 / 2) ∨ (x, y, z) = (3 / 2, -1, -1) ∨ (x, y, z) = (-1, 3 / 2, -1) := by

    -- we can combine first two equations
    have h0: (z-x)*(1/((x+y)*(y+z))+1)=0 := by
      have h1: 1/(x+y)+z - (1/(y+z)+x) = 1-1 := by linarith
      rw [sub_self] at h1
      rw [← h1]
      apply Eq.symm
      calc 1 / (x + y) + z - (1 / (y + z) + x)
      _ = 1 / (x + y) + z - 1 / (y + z) - x := by ring_nf
      _ = 1 / (x + y)- 1 / (y + z)   +  (z-x) := by ring_nf
      _ = ((y + z)/(y + z)) / (x + y) - ((x + y)/(x + y)) / (y + z)   +  (z-x) := by rw [div_self (by intro h; apply h₁; linarith;), div_self (by intro h; apply h₀; linarith)]
      _ = (y + z)/((y + z)*(x + y)) - (x + y)/((x + y)*(y + z))   +  (z-x) := by rw [div_div, div_div]
      _ = (z - x) * (1 / ((x + y) * (y + z)) + 1) := by ring_nf
    -- same for other two options
    have h1: (y-z)*(1/((z+x)*(x+y))+1)=0 := by
      have h2: 1/(z+x)+y - (1/(x+y)+z) = 1-1 := by linarith
      rw [sub_self] at h2
      rw [← h2]
      apply Eq.symm
      calc 1 / (z + x) + y - (1 / (x + y) + z)
      _ = 1 / (z + x) + y - 1 / (x + y) - z := by ring_nf
      _ = 1 / (z + x)- 1 / (x + y)   +  (y-z) := by ring_nf
      _ = ((x + y)/(x + y)) / (z + x) - ((z + x)/(z + x)) / (x + y)   +  (y-z) := by rw [div_self (by intro h; apply h₀; linarith), div_self (by intro h; apply h₂; linarith)]
      _ = (x + y)/((x + y)*(z + x)) - (z + x)/((z + x)*(x + y))   +  (y-z) := by rw [div_div, div_div]
      _ = (y - z) * (1 / ((z + x) * (x + y)) + 1) := by ring_nf

    have h2: (x-y)*(1/((y+z)*(z+x))+1)=0 := by
      have h3: 1/(y+z)+x - (1/(z+x)+y) = 1-1 := by linarith
      rw [sub_self] at h3
      rw [← h3]
      apply Eq.symm
      calc 1 / (y + z) + x - (1 / (z + x) + y)
      _ = 1 / (y + z) + x - 1 / (z + x) - y := by ring_nf
      _ = 1 / (y + z)- 1 / (z + x)   +  (x-y) := by ring_nf
      _ = ((z + x)/(z + x)) / (y + z) - ((y + z)/(y + z)) / (z + x)   +  (x-y) := by rw [div_self (by intro h; apply h₂; linarith), div_self (by intro h; apply h₁; linarith)]
      _ = (z + x)/((z + x)*(y + z)) - (y + z)/((y + z)*(z + x))   +  (x-y) := by rw [div_div, div_div]
      _ = (x - y) * (1 / ((y + z) * (z + x)) + 1) := by ring_nf

    simp at h0 h1 h2
    -- now we need to split by case of whether or not they are all distinct
    have h3: (x≠y ∧ y≠z ∧ z ≠x) ∨ ¬(x≠y ∧ y≠z ∧ z ≠x) := by apply Classical.em
    cases' h3 with h3 h3
    · obtain ⟨h3xy, h3yz, h3zx⟩ := h3
      -- if they are all distinct, then we can divide by the factors
      cases' h0 with h0 h0
      exfalso; apply h3zx; linarith
      cases' h1 with h1 h1
      exfalso; apply h3yz; linarith
      cases' h2 with h2 h2
      exfalso; apply h3xy; linarith
      apply congr_arg (fun x => (x-1)⁻¹) at h0
      apply congr_arg (fun x => (x-1)⁻¹) at h1
      apply congr_arg (fun x => (x-1)⁻¹) at h2
      simp at h0 h1 h2; norm_num at h0 h1 h2; ring_nf at h0 h1 h2
      -- this gives x^2=y^2=z^2
      -- either one gives contradition immediatly
      exfalso
      apply congr_arg (fun t => t-x*y-y*z-z*x) at h0
      apply congr_arg (fun t => t-x*y-y*z-z*x) at h1
      ring_nf at h0 h1
      have h2:x^2=y^2 := by linarith
      apply sq_eq_sq_iff_eq_or_eq_neg.mp at h2
      aesop
    -- then we check the case where they are all equal
    have h4: (x = y ∧ y = z ∧ z = x) ∨ ¬(x = y ∧ y = z ∧ z = x) := by apply Classical.em
    cases' h4 with h4 h4
    · obtain ⟨h4xy, h4yz, h4zx⟩ := h4
      -- not much of a system then, just solve one equation
      rw [h4yz, h4zx] at h₃
      simp at h₃
      apply congr_arg (fun t => t*x) at h₃
      ring_nf at h₃
      rw [mul_inv_cancel₀ (by intro h; rw [h] at h4xy; apply h₀; linarith)] at h₃
      apply congr_arg (fun t => t-x) at h₃
      ring_nf at h₃
      -- this quadratic is not solvable
      exfalso
      refine quadratic_ne_zero_of_discrim_ne_sq (a:=1) (b:=-1) (c:=1/2) ?_ x ?_
      rotate_left; ring_nf; assumption
      intro s; unfold discrim; norm_num
      suffices 0 ≤ s^2 by linarith
      exact sq_nonneg s
    -- now we know they are not all equal but also not all different. Let's cover the other cases
    wlog hxy:x≠y;
    specialize this (y:=x) (z:=y) (x:=z) h₂ h₀ h₁ h₅ h₃ h₄ h1 h2 h0
    suffices t1:¬(z ≠ x ∧ x ≠ y ∧ y ≠ z) by
      specialize this t1
      suffices t2:¬(z = x ∧ x = y ∧ y = z) by
        specialize this t2
        suffices t3:z≠x by
          specialize this t3
          aesop
        by_contra h
        aesop
      aesop
    aesop
    right
    wlog hyz:y=z;
    · specialize this (x:=y) (y:=x) (z:=z)
      simp at hyz hxy h3
      specialize h3 hxy hyz
      rw [h3] at this h₂ h₁ h₅ h₃ h₄ h1 h2 h4 hyz ⊢
      specialize this h₁ h₂ h₀ h₄ h₅ h₃ h2 (by left; simp) h1 (by simp) (by simp; intro h; trivial) hyz (by trivial)
      aesop
    left
    -- now we know that x≠y so we can eliminate a branch at h2
    cases' h2 with h2 h2
    · exfalso
      apply hxy; linarith
    apply congr_arg (fun x => (x-1)⁻¹) at h2
    rw [hyz] at h2 h₄
    ring_nf at h2 h₄; simp at h2
    -- now we just solve the system
    have h5:x = 1 - z⁻¹/2 := by linarith
    rw [h5] at h2
    conv_lhs at h2 =>
      calc _
      _ = 2*z^2 + 2*z - z*z⁻¹ := by ring_nf
      _ = 2*z^2 + 2*z - 1 := by rw [mul_inv_cancel₀ (by intro h; rw [h] at hyz; apply h₁; linarith)]
    apply congr_arg (fun x => (x+1)/z) at h2
    ring_nf at h2
    conv_lhs at h2 =>
      calc _
      _ = 2 + 2 * z^2 * z⁻¹ := by rw [mul_inv_cancel₀ (by intro h; rw [h] at hyz; apply h₁; linarith)]; ring_nf
      _ = 2 + 2 * z*(z* z⁻¹) := by ring_nf
      _ = 2 + 2 * z := by rw [mul_inv_cancel₀ (by intro h; rw [h] at hyz; apply h₁; linarith), mul_one]
    have hz:z=-1:= by linarith
    rw [hz] at h₄; ring_nf at h₄
    simp
    constructor
    linarith
    constructor
    linarith
    linarith