import Mathlib

open Real

-- Example 11 (9th American Invitational Mathematics Examination) How many real numbers $a$ are there such that $x^{2}+a x+6 a=0$ has only integer solutions.
-- =10solution
-- 解 设方程 $x^{2}+a x+6 a=0$ 有整数解 $m, n(m \leqslant n)$, 则有 $$ \begin{array}{l} m+n=-a, \\ m n=6 a . \end{array} $$

-- 于是有 $-6(m+n)=m n$, 即 $$ (m+6)(n+6)=36 \text {. } $$

-- 因为 $36=1 \cdot 36=2 \cdot 18=3 \cdot 12=4 \cdot 9=6 \cdot 6$, 所以 满足 $m \leqslant n$ 的解 $(m, n)$ 有 $$ \begin{array}{l} (-42,-7),(-24,-8),(-18,-9),(-15,-10), \\ (-12,-12),(-5,30),(-4,12),(-3,6),(-2,3),(0,0) . \end{array} $$

-- 对应的 $a=-(m+n)$ 的值为 $$ 49,32,27,25,24,-25,-8,-3,-1,0 \text {. 共 } 10 \text { 个. } $$



theorem algebra_236268 :
  {a : ℝ | (∃ x : ℝ, x^2 + a * x + 6 * a = 0) ∧ (∀ x : ℝ, x^2 + a * x + 6 * a = 0 → ∃ n : ℤ, x = n)}.encard = 10 := by

  suffices {a : ℝ | (∃ x : ℝ, x^2 + a * x + 6 * a = 0) ∧ (∀ x : ℝ, x^2 + a * x + 6 * a = 0 → ∃ n : ℤ, x = n)} = {-25,-8,-3,-1,0,24,25,27,32,49} by
    rw [this]
    repeat rw [Set.encard_insert_of_not_mem]
    all_goals simp
    all_goals norm_num

  ext a
  simp
  refine Iff.intro ?_ $ by
    intro ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    . constructor
      . use -5; norm_num
      . intro x hx
        have : x^2 + -25 * x + 6 * -25 = 0 := hx
        have : (x + 5) * (x - 30) = 0 := by linarith
        simp at this
        rcases this with hx1 | hx2
        . have : x = -5 := by linarith
          use -5; subst x; norm_cast
        . have : x = 30 := by linarith
          use 30; subst x; norm_cast
    . constructor
      . use -4; norm_num
      . intro x hx
        have : x^2 + -8 * x + 6 * -8 = 0 := hx
        have : (x + 4) * (x - 12) = 0 := by linarith
        simp at this
        rcases this with hx1 | hx2
        . have : x = -4 := by linarith
          use -4; subst x; norm_cast
        . have : x = 12 := by linarith
          use 12; subst x; norm_cast
    . constructor
      . use -3; norm_num
      . intro x hx
        have : x^2 + -3 * x + 6 * -3 = 0 := hx
        have : (x + 3) * (x - 6) = 0 := by linarith
        simp at this
        rcases this with hx1 | hx2
        . have : x = -3 := by linarith
          use -3; subst x; norm_cast
        . have : x = 6 := by linarith
          use 6; subst x; norm_cast
    . constructor
      . use -2; norm_num
      . intro x hx
        have : x^2 + -1 * x + 6 * -1 = 0 := hx
        have : (x + 2) * (x - 3) = 0 := by linarith
        simp at this
        rcases this with hx1 | hx2
        . have : x = -2 := by linarith
          use -2; subst x; norm_cast
        . have : x = 3 := by linarith
          use 3; subst x; norm_cast
    . constructor
      . use 0; norm_num
      . intro x hx
        have : x^2 + 0 * x + 6 * 0 = 0 := hx
        simp at this
        use 0; subst x; norm_cast
    . constructor
      . use -12; norm_num
      . intro x hx
        have : x^2 + 24 * x + 6 * 24 = 0 := hx
        have : (x + 12)^ 2 = 0 := by linarith
        simp at this
        have : x = -12 := by linarith
        use -12; subst x; norm_cast
    . constructor
      . use -10; norm_num
      . intro x hx
        have : x^2 + 25 * x + 6 * 25 = 0 := hx
        have : (x + 10)*(x + 15) = 0 := by linarith
        simp at this
        rcases this with hx1 | hx2
        . have : x = -10 := by linarith
          use -10; subst x; norm_cast
        . have : x = -15 := by linarith
          use -15; subst x; norm_cast
    . constructor
      . use -9; norm_num
      . intro x hx
        have : x^2 + 27 * x + 6 * 27 = 0 := hx
        have : (x + 9)*(x + 18) = 0 := by linarith
        simp at this
        rcases this with hx1 | hx2
        . have : x = -9 := by linarith
          use -9; subst x; norm_cast
        . have : x = -18 := by linarith
          use -18; subst x; norm_cast
    . constructor
      . use -8; norm_num
      . intro x hx
        have : x^2 + 32 * x + 6 * 32 = 0 := hx
        have : (x + 8)*(x + 24) = 0 := by linarith
        simp at this
        rcases this with hx1 | hx2
        . have : x = -8 := by linarith
          use -8; subst x; norm_cast
        . have : x = -24 := by linarith
          use -24; subst x; norm_cast
    . constructor
      . use -7; norm_num
      . intro x hx
        have : x^2 + 49 * x + 6 * 49 = 0 := hx
        have : (x + 7)*(x + 42) = 0 := by linarith
        simp at this
        rcases this with hx1 | hx2
        . have : x = -7 := by linarith
          use -7; subst x; norm_cast
        . have : x = -42 := by linarith
          use -42; subst x; norm_cast

  intro ⟨hx1, hx2⟩

  have ha1 : a ≤ 0 ∨ 24 ≤ a := by
    by_contra h
    simp at h
    have ⟨h1, h2⟩ := h
    obtain ⟨x, hx⟩ := hx1

    have : x^2 = -a*x - 6*a := by linarith
    have : (x+a/2)^2 = a^2/4 - 6*a := by
      ring_nf
      rw [this]
      linarith

    have : (x+a/2)^2 ≥ 0 := by positivity
    nlinarith

  have ha2 : a*(a-24) ≥ 0 := by
    rcases ha1 with h|h
    . nlinarith
    . nlinarith

  let x1 := -a/2 - √(a^2 - 24 * a)/2
  let x2 := -a/2 + √(a^2 - 24 * a)/2

  have hx1_eq : x1^2 + a * x1 + 6 * a = 0 := by
    unfold x1
    ring_nf
    rw [sq_sqrt (by linarith)]
    ring_nf

  have hx2_eq : x2^2 + a * x2 + 6 * a = 0 := by
    unfold x2
    ring_nf
    rw [sq_sqrt (by linarith)]
    ring_nf

  obtain ⟨n1, hn1⟩ := hx2 x1 hx1_eq
  obtain ⟨n2, hn2⟩ := hx2 x2 hx2_eq

  have hx3 : x1 + x2 = -a := by
    unfold x1 x2
    ring_nf

  have hx4 : x1 * x2 = 6 * a := by
    unfold x1 x2
    ring_nf
    rw [sq_sqrt (by linarith)]
    ring_nf

  have hx5 : 6 * (x1 + x2) = -x1 * x2 := by
    linarith

  have hx6 : (x1 + 6) * (x2 + 6) = 36 := by
    linarith

  rw [hn1, hn2] at hx6
  norm_cast at hx6


  let m1 := n1 + 6
  let m2 := n2 + 6

  have hm12: m1+m2 ∈ ({-37, -20, -15, -13, -12, 12, 13, 15, 20, 37}: Set ℤ):= by
    simp

    have hm : m1 * m2 = 36 := by
      unfold m1 m2
      exact hx6

    have hm1 : m1 ∣ 36 := by
      use m2
      linarith

    have hm2 : m1 ≤ 36 := by
      apply Int.le_of_dvd (by norm_num) hm1

    have hm3 : -m1 ∣ 36 := by
      exact Int.neg_dvd.2 hm1

    have hm4 : -m1 ≤ 36 := by
      apply Int.le_of_dvd (by norm_num) hm3

    have hm5 : m1 ≥ -36 := by
      linarith

    interval_cases m1 <;> omega

  have : a = 12-(m1+m2) := by
    unfold m1 m2
    push_cast
    rw [← hn1, ← hn2]
    linarith

  norm_cast at this
  rcases hm12 with h|h|h|h|h|h|h|h|h|h
  all_goals try simp at h
  all_goals rw [h] at this; norm_num at this; subst a; simp
