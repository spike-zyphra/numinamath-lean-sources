import Mathlib

open Real Set

/- Given the function defined on $\mathbf{R}^{+}$ as $f(x)=\left\{\begin{array}{ll}\left|\log _{3} x-1\right|,
& 09 .\end{array}\right.$ Let $a, b, c$ be three distinct real numbers, satisfying $f(a)=f(b)=f(c)$, find the range of $a b c$.
-/

theorem algebra_268175 {f : ℝ → ℝ}
  (h1: ∀ x, 0 < x → x < 9 → f x = abs (logb 3 x - 1))
  (h2: ∀ x, 9 ≤ x → f x = 4 - √x):
  {x: ℝ | ∃ a b c : ℝ, 0 < a ∧ a < b ∧ b < c ∧ f a = f b ∧ f b = f c ∧ x = a * b * c} = Ioo 81 144 := by

  ext x
  constructor

  -- the forward direction
  .
    intro h
    rw [Set.mem_setOf] at h
    obtain ⟨a, b, c, l1, l2, l3, f1, f2, rfl⟩ := h
    simp
    have y3: f a = f c:= by linarith

    -- we first show that b < 9
    have lb: b < 9 := by
      by_contra! o
      have g1:= h2 b (by linarith)
      have g2:= h2 c (by linarith)
      simp [g1, g2] at f2
      rw [Real.sqrt_inj] at f2
      linarith
      linarith
      linarith

    have fa:= h1 a (by linarith) (by linarith)
    have fb:= h1 b (by linarith) (by linarith)

    -- then we show that a ≤ 3
    have ra: a ≤ 3 := by
      by_contra! o
      have u: 1 ≤ logb 3 a := by
        rw [Real.le_logb_iff_rpow_le]
        linarith
        norm_num
        linarith
      have v: 1 ≤ logb 3 b:= by
        rw [Real.le_logb_iff_rpow_le]
        linarith
        norm_num
        linarith
      rw [fa, fb] at f1
      clear fa fb f2 l3
      rw [show |logb 3 a - 1| = logb 3 a - 1 by apply abs_of_nonneg; linarith] at f1
      rw [show |logb 3 b - 1| = logb 3 b - 1 by apply abs_of_nonneg; linarith] at f1
      replace f1: logb 3 b ≤ logb 3 a := by
        clear *- f1
        linarith
      replace f1: b ≤ a := by
        rw [Real.logb_le_logb] at f1
        tauto
        norm_num
        linarith
        tauto
      linarith

    have ua: logb 3 a ≤ 1 := by
      have o: 1 = logb 3 3 := by
        norm_num
      rw [o]
      apply Real.logb_le_logb_of_le
      norm_num
      tauto
      tauto
    rw [show |logb 3 a - 1| = -(logb 3 a - 1) by apply abs_of_nonpos; linarith] at fa

    -- similarly, we show that 3 ≤ b
    have rb: 3 ≤ b := by
      by_contra! o
      have u: logb 3 b ≤ 1:= by
        have o: 1 = logb 3 3 := by
          norm_num
        rw [o]
        apply Real.logb_le_logb_of_le
        norm_num
        linarith
        linarith
      rw [show |logb 3 b - 1| = -(logb 3 b - 1) by apply abs_of_nonpos; linarith] at fb
      replace f1: logb 3 b ≤ logb 3 a := by
        linarith
      replace f1: b ≤ a := by
        rw [Real.logb_le_logb] at f1
        tauto
        norm_num
        linarith
        tauto
      linarith
    have u: 1 ≤ logb 3 b:= by
      have o: 1 = logb 3 3 := by
        norm_num
      rw [o]
      apply Real.logb_le_logb_of_le
      norm_num
      linarith
      linarith
    rw [show |logb 3 b - 1| = (logb 3 b - 1) by apply abs_of_nonneg; linarith] at fb

    simp [fa, fb] at f1
    replace f1: logb 3 a + logb 3 b = 2 := by
      linarith
    rw [← Real.logb_mul] at f1
    have o: 2 = logb 3 9 := by
      symm
      rw [Real.logb_eq_iff_rpow_eq]
      norm_num
      norm_num
      norm_num
      norm_num
    rw [o] at f1
    clear o

    -- then we show that ab = 9
    have s: a * b = 9 := by
      have g1: logb 3 (a * b) ≤ logb 3 9 := by
        rw [f1]
      have g2: logb 3 9 ≤ logb 3 (a * b) := by
        rw [f1]
      rw [Real.logb_le_logb] at g1 g2
      linarith
      norm_num
      norm_num
      nlinarith
      norm_num
      nlinarith
      norm_num

    rw [show a * b * c = (a * b) * c by ring]
    simp [s]

    have oa: 0 < f a := by
      have v: 0 ≤ f a := by linarith
      have v1: f a ≠ 0 := by
        by_contra! o
        simp [fa] at o
        replace o: logb 3 a = 1 := by linarith
        rw [Real.logb_eq_iff_rpow_eq] at o
        simp at o
        simp [← o] at s
        clear *- s o l2
        nlinarith
        norm_num
        norm_num
        tauto
      by_contra! O
      replace O: f a = 0 := by linarith
      tauto

    -- we show that 9 < c
    have lc: 9 < c := by
      by_contra! l
      have f3:= h1 c (by linarith)
      replace f3: f c = |logb 3 c - 1| := by
        by_cases q: c = 9
        .
          specialize h2 9 (by norm_num)
          rw [q]
          have o: 2 = logb 3 9 := by
            symm
            rw [Real.logb_eq_iff_rpow_eq]
            norm_num
            norm_num
            norm_num
            norm_num
          rw [← o]
          simp [h2]
          have u: √9 = 3 := by
           rw [Real.sqrt_eq_iff_mul_self_eq]
           norm_num
           norm_num
           norm_num
          simp [u]
          norm_num
        .
          replace q: c < 9 := by
            by_contra! o
            replace o: c = 9 := by linarith
            tauto
          exact h1 c (by linarith) (by linarith)
      by_cases q: logb 3 c < 1
      .
        rw [show |logb 3 c - 1| = -(logb 3 c - 1) by apply abs_of_nonpos; linarith] at f3
        simp [f3, fa] at y3
        replace y3: logb 3 c ≤ logb 3 a := by
          rw [y3]
        rw [Real.logb_le_logb] at y3
        linarith
        norm_num
        linarith
        tauto
      .
        simp at q
        rw [show |logb 3 c - 1| = (logb 3 c - 1) by apply abs_of_nonneg; linarith] at f3
        simp [f3, fb] at f2
        replace f2: logb 3 c ≤ logb 3 b := by
          linarith
        rw [Real.logb_le_logb] at f2
        linarith
        norm_num
        linarith
        linarith

    refine ⟨(by linarith), ?_⟩
    
    -- finally, we show that c < 16
    specialize h2 c (by linarith)

    rw [← y3] at h2
    rw [h2] at oa
    replace oa: √c < 4 := by
      linarith
    rw [Real.sqrt_lt'] at oa
    clear *- oa
    nlinarith
    norm_num
    linarith
    linarith


  -- the backward direction, we need to construct a, b, c to obtain any x ∈ (81, 144)
  .
    intro h
    simp at h
    rw [Set.mem_setOf]
    set y:= 4 - √x / 3
    have l1: 0 < y := by
      simp [y]
      suffices √x < 12 by linarith
      rw [Real.sqrt_lt']
      linarith
      norm_num
    have l2: y < 1 := by
      simp [y]
      suffices 9 < √x by linarith
      rw [Real.lt_sqrt]
      linarith
      norm_num

    -- construct a b c
    set a:= (3: ℝ) ^ (1 - y)
    set b:= (3: ℝ) ^ (1 + y)
    set c:= x / 9
    use a, b, c

    -- show that they satisfy the conditions
    have la: 0 < a := by
      simp [a]
      apply Real.rpow_pos_of_pos
      norm_num
    have lb: b < 9 := by
      simp [b]
      rw [show 9 = (3: ℝ) ^ ( 2: ℝ)by norm_num]
      rw [Real.rpow_lt_rpow_left_iff]
      linarith
      norm_num
    have lc: 9 < c := by
      simp [c]
      linarith
    have l: a < b := by
      simp [a, b]
      linarith
    have ra: logb 3 a ≤ 1 := by
      have o: 1 = logb 3 3 := by
        norm_num
      rw [o]
      apply Real.logb_le_logb_of_le
      norm_num
      linarith
      simp [a]
      nth_rewrite 2 [show 3 = (3: ℝ) ^ (1: ℝ) by norm_num]
      rw [Real.rpow_le_rpow_left_iff]
      linarith
      norm_num
    have fa:= h1 a (by linarith) (by linarith)
    have fb:= h1 b (by linarith) (by linarith)
    rw [show |logb 3 a - 1| = -(logb 3 a - 1) by apply abs_of_nonpos; linarith] at fa
    have rb: 1 ≤ logb 3 b := by
      have o: 1 = logb 3 3 := by
        norm_num
      rw [o]
      apply Real.logb_le_logb_of_le
      norm_num
      linarith
      simp [b]
      nth_rewrite 1 [show 3 = (3: ℝ) ^ (1: ℝ) by norm_num]
      rw [Real.rpow_le_rpow_left_iff]
      linarith
      norm_num
    rw [show |logb 3 b - 1| = (logb 3 b - 1) by apply abs_of_nonneg; linarith] at fb

    refine ⟨la, l, (by linarith), ?_, ?_, ?_⟩

    -- show that fa = fb
    .
      simp [fa, fb]
      suffices logb 3 a + logb 3 b = 2 by linarith
      rw [← Real.logb_mul]
      simp [a, b]
      rw [← Real.rpow_add]
      ring_nf
      rw [Real.logb_eq_iff_rpow_eq]
      norm_num
      norm_num
      norm_num
      norm_num
      linarith
      linarith
      linarith

    -- show that fb = fc
    .
      specialize h2 c (by linarith)
      simp [fb, h2]
      simp [c]
      have z: √9 = 3 := by
        rw [Real.sqrt_eq_iff_mul_self_eq_of_pos]
        norm_num
        norm_num
      rw [z]
      suffices logb 3 b = 1 + y by
        simp [y] at this
        linarith
      rw [Real.logb_eq_iff_rpow_eq]
      norm_num
      linarith
      linarith

    -- show that x = abc
    .
      have s: a * b = 9 := by
        simp [a, b]
        rw [← Real.rpow_add]
        ring_nf
        norm_num
      rw [show a * b * c = (a * b) * c by ring]
      rw [s]
      simp [c]
      ring