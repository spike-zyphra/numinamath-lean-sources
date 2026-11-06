import Mathlib

/- Let a, b, c and d be real numbers that satisfy the system of equations
a + b = -3
ab + bc + ca = -4
abc + bcd + cda + dab = 14
abcd = 30
There exist relatively prime positive integers m and n such that
a^2 + b^2 + c^2 + d^2 = m/n
Find m + n. -/
theorem algebra_98584 (a b c d : ℝ)
(h₀ : a + b = -3)
(h₁ : a * b + b * c + c * a = -4)
(h₂ : a * b * c + b * c * d + c * d * a + d * a * b = 14)
(h₃ : a * b * c * d = 30) :
∃ m n : ℕ, m > 0 ∧ n > 0 ∧ Nat.Coprime m n ∧
a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = m / n := by
  -- we first show that a, b, c are not equal to 0
  have ha: a≠0 := by
    intro ha; rw[ha] at h₀ h₁ h₂ h₃; linarith
  have hb: b≠0 := by
    intro hb; rw[hb] at h₀ h₁ h₂ h₃; linarith
  have hc: c≠0 := by
    intro hc; rw[hc] at h₁ h₂ h₃; linarith
  have hd: d≠0 := by
    intro hd; rw[hd] at h₃; linarith
  -- Now we can compute d from h₃ and plug it into the other equations
  have hd30: d = 30 / (a * b * c) := by
    rw [mul_comm] at h₃
    exact eq_div_of_mul_eq (by simp; refine ⟨⟨by intro ha'; exact ha ha', by intro hb'; exact hb hb'⟩ , by intro hc'; exact hc hc'⟩;) h₃
  rw [hd30] at h₂
  conv_lhs at h₂ =>
    calc a * b * c + b * c * (30 / (a * b * c)) + c * (30 / (a * b * c)) * a + 30 / (a * b * c) * a * b
    _ = a * b * c + 30 * (a*b+b*c+c*a) / (a*b*c) := by ring_nf
    _ = a * b * c + 30 * (-4) / (a*b*c) := by rw [h₁]
    _ = a * b * c - 120 / (a*b*c) := by ring_nf
  -- now we solve for abc in h₂
  let habc: ∃ abc : ℝ, a * b * c = abc := by
    use a*b*c
  obtain ⟨abc, habc⟩ := habc
  rw [habc] at h₂
  apply congr_arg (fun x=> x * abc - 14 * abc) at h₂
  ring_nf at h₂
  -- to be able to cancel we have to show abc ≠ 0
  have habc0: abc ≠ 0 := by
    intro habc0; rw [← habc] at habc0; rw [habc0] at hd30; simp at hd30; exact hd hd30
  rw [mul_inv_cancel₀ habc0] at h₂
  ring_nf at h₂
  -- we get a quadratic equation in abc
  have sol := (quadratic_eq_zero_iff (a:=(1:ℝ)) (b:=(-14:ℝ)) (c:=(-120:ℝ)) (by norm_num) (s:=26) (by unfold discrim; norm_num) abc).mp
  ring_nf at sol
  have sol' := sol h₂
  -- rw h₀ at h₁ to prepare to substitute abc
  conv_lhs at h₁ =>
    calc a*b + b*c + c*a
    _ = a*b + c*(a+b) := by ring_nf
    _ = a*b -3 *c := by rw [h₀]; ring_nf
  have h₁_bak := h₁
  -- we multiply both sides by c to get abc term and move all other terms to the right
  apply congr_arg (fun x => x * c + 3 * c^2) at h₁
  ring_nf at h₁

  -- now we are ready to analyze cases for abc
  cases' sol' with sol1 sol2
  -- we get two solutions: 20 and -6. Let's show -6 is not possible
  rotate_left
  · rw [habc, sol2] at h₁
    apply congr_arg (fun x=> 6+x) at h₁
    ring_nf at h₁
    -- let's show this quadratic has no real roots
    have sol2 := quadratic_ne_zero_of_discrim_ne_sq (a:=3) (b:=-4) (c:=6) (by
      intro s; unfold discrim; norm_num;
      intro hs
      have q: IsSquare (s^2) := by
        use s; ring_nf
      have q2:= IsSquare.nonneg q
      linarith
      ) c
    ring_nf at sol2
    symm at h₁
    exfalso
    exact sol2 h₁
  -- so we get abc = 20
  rw [← habc] at sol1
  rw [sol1] at hd30 h₁
  -- solving for d is easy
  norm_num at hd30
  -- we have quadratic equation in c at h₁
  apply congr_arg (fun x => x - 20) at h₁
  ring_nf at h₁
  have sol := (quadratic_eq_zero_iff (a:=(3:ℝ)) (b:=(-4:ℝ)) (c:=(-20:ℝ)) (by norm_num) (s:=16) (by unfold discrim; norm_num) c).mp
  ring_nf at sol
  symm at h₁
  have hb':b=-3-a:= by linarith
  cases' sol h₁ with sol1 sol2
  -- we get c=10/3 or c=-2. First option doesn't give solutions for a, b so we go by contradiction again
  · rw [sol1, hb'] at h₁_bak
    apply congr_arg (fun x => x+4) at h₁_bak
    ring_nf at h₁_bak
    -- we once again show this quadratic has no real roots
    have sol1 := quadratic_ne_zero_of_discrim_ne_sq (a:=-1) (b:=-3) (c:=-6) (by
      unfold discrim; norm_num; intro s hs
      have q: IsSquare (s^2) := by
        use s; ring_nf
      have q2:= IsSquare.nonneg q
      linarith
      ) a
    ring_nf at sol1 h₁_bak
    exfalso
    exact sol1 h₁_bak
  -- with c=-2 we can proceed
  rw [sol2, hb'] at h₁_bak
  apply congr_arg (fun x => x+4) at h₁_bak
  ring_nf at h₁_bak
  -- we get a quadratic equation in a
  have sol := (quadratic_eq_zero_iff (a:=(-1:ℝ)) (b:=(-3:ℝ)) (c:=(10:ℝ)) (by norm_num) (s:=7) (by unfold discrim; norm_num) a).mp
  ring_nf at sol
  have sol' := sol h₁_bak
  cases' sol' with sol1 sol1
  -- turns out a^2+b^2 is independent of solution choice so we can shorten a bit
  all_goals {
    rw [sol1] at hb'
    norm_num at hb'
    rw [sol1, hb', sol2, hd30]; norm_num; use 141, (by norm_num), 4, (by norm_num); norm_num
  }