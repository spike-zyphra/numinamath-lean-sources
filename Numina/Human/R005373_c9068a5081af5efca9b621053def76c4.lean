import Mathlib

/- Let $f$ be a function defined in the set $\{0,1,2, \ldots\}$ of non-negative integers, satisfying
$f(2 x)=2 f(x), f(4 x+1)=4 f(x)+3$, and $f(4 x-1)=2 f(2 x-1)-1$.
Show that $f$ is an injection, i.e. if $f(x)=f(y)$, then $x=y$. -/
theorem number_theory_607959 (f : ℕ → ℕ) (h1 : ∀ x, f (2 * x) = 2 * f x) (h2 : ∀ x, f (4 * x + 1) = 4 * f x + 3)
(h3 : ∀ x, f (4 * x - 1) = 2 * f (2 * x - 1) - 1)  (h4 : ∀ x, x ≠ 0 → f x ≠ 0):
    Function.Injective f := by
  have h_even: ∀ x: ℕ, 2 ∣ x  →  2 ∣f x  := by
    intro x
    have h1_2:= h1
    specialize h1 x
    intro y
    apply exists_eq_mul_right_of_dvd at y
    obtain ⟨t, ht⟩ := y
    rw [ht]
    specialize h1_2 t
    rw [h1_2]
    apply Nat.dvd_mul_right
    -- This is the key lemma to prove the injectivity of f --
  have h_odd: ∀ x: ℕ, 2 ∣ x + 1  →  2 ∣f x + 1 := by
    intro x
    -- split into four cases according to the remainder of x mod 4 --
    have case: (4 ∣ x) ∨ (4 ∣ x + 1) ∨ (4 ∣ x + 2) ∨ (4 ∣ x + 3) := by omega
    rcases case with c1 | c2 | c3 | c4
    . intro z
      replace c1: 2 ∣ x := by omega
      have contra: 2 ∣ 1 := by omega
      tauto
    . apply exists_eq_mul_right_of_dvd at c2
      obtain ⟨t, ht⟩ := c2
      replace c2: x = 4 * t - 1 := by omega
      have h3_2:= h3
      specialize h3 t
      rw [← c2] at h3
      rw [h3]
      intro a
      have w: 2 * f (2 * t - 1) - 1 + 1 = 2 * f (2 * t - 1) := by
        apply Nat.sub_add_cancel
        by_contra! q
        replace q: f (2 * t - 1) = 0 := by omega
        specialize h4 (2 * t - 1)
        have v: 2 * t - 1 ≠ 0 := by
          by_contra! r
          omega
        simp [v] at h4
        tauto
      rw [w]
      apply Nat.dvd_mul_right
    . apply exists_eq_mul_right_of_dvd at c3
      obtain ⟨t, ht⟩ := c3
      replace c2: x = 2 * (2 * t - 1) := by omega
      intro a
      rw [c2] at a
      have contra: 2 ∣ 1 := by omega
      tauto
    . apply exists_eq_mul_right_of_dvd at c4
      obtain ⟨t, ht⟩ := c4
      have t1: 1 ≤ t := by
        by_contra! t1
        replace t1: t = 0 := by omega
        rw [t1] at ht
        simp at ht
      let k:= t - 1
      replace ht: x = 4 * k + 1 := by omega
      specialize h2 k
      rw [← ht] at h2
      intro r
      rw [h2]
      rw [show 4 * f k + 3 + 1 = 2 * (2 * f k + 2) by omega]
      apply Nat.dvd_mul_right
  -- 4 ∣ x + 1 → 4 ∣ f x + 3 -- 
  have h_mod4_3: ∀ (x: ℕ), 4 ∣ x + 1 → 4 ∣ f x + 3 := by
    intro x
    intro h
    have x1:= h
    apply exists_eq_mul_right_of_dvd at h
    obtain ⟨t,ht⟩:= h
    specialize h3 t
    replace ht: x = 4 * t - 1 := by omega
    rw [← ht] at h3
    rw [h3]
    specialize h_odd (2 * t - 1)
    have o: 2 ∣ 2 * t - 1 + 1 := by
      rw [Nat.sub_add_cancel]
      apply Nat.dvd_mul_right
      have v: 1 ≤ t := by
        by_contra! c
        replace v: t = 0 := by omega
        rw [v] at ht
        simp at ht
        rw [ht] at x1
        omega
      omega
    simp [o] at h_odd
    omega
  -- 4 ∣ x + 3 → 4 ∣ f x + 1 --
  have h_mod4_1: ∀ (x: ℕ), 4 ∣ x + 3 → 4 ∣ f x + 1 := by
    intro x
    intro h
    have x1:= h
    apply exists_eq_mul_right_of_dvd at h
    obtain ⟨t,ht⟩:= h
    let r:= t - 1
    specialize h2 r
    replace ht: x = 4 * r + 1 := by omega
    rw [← ht] at h2
    rw [h2]
    omega
  -- a technical lemma --
  have key_lemma: ∀ k: ℕ,(∀ x y: ℕ, (x < k) ∧ (y < k) ∧ (f x = f y) → x = y) → (∀ x y: ℕ, (x < 2 * k) ∧ (y < 2 * k) ∧ (f x = f y) → x = y) := by
    intro k
    intro u
    intro x y
    intro o
    rcases o with ⟨b1,b2,l⟩
    have cases: (4 ∣ x) ∨ (4 ∣ x + 1) ∨ (4 ∣ x + 2) ∨ (4 ∣ x + 3) := by
      omega
    rcases cases with c1 | c2 | c3 | c4
    -- cases c1: 4 ∣ x --
    . replace c1: 2 ∣ x := by
        apply exists_eq_mul_right_of_dvd at c1
        obtain ⟨t, ht⟩ := c1
        rw [ht]
        rw [show 4 * t = 2 * (2 * t) by ring]
        apply Nat.dvd_mul_right
      specialize h_even x
      apply exists_eq_mul_right_of_dvd at c1
      obtain ⟨t, ht⟩ := c1
      have h_even1:= h_even
      have x1: 2 ∣ x := by rw [ht]; apply Nat.dvd_mul_right
      simp [ht] at h_even
      rw [ht] at l
      rw [l] at h_even
      have y1: 2 ∣ y := by
        by_contra! y1
        have y2: 2 ∣ y + 1 := by omega
        specialize h_odd y
        simp [y2] at h_odd
        have contra: 2 ∣ 1 := by omega
        tauto
      apply exists_eq_mul_right_of_dvd at y1
      obtain ⟨s, hs⟩ := y1
      have t1: t < k := by omega
      have t2: s < k := by omega
      specialize u t s
      simp [t1,t2] at u
      have h1_1:= h1
      specialize h1 t
      specialize h1_1 s
      have eq: 2 * f t =2 * f s := by
        calc
          2 * f t = f (2 * t) := by omega
                 _= f y := by omega
                 _= f (2 * s) := by rw [hs]
                 _= 2 * f s := by omega
      replace eq: f t =f s := by omega
      simp [eq] at u
      omega
      -- cases c2: 4 ∣ x + 1 --
    . have h_mod4_3_2:= h_mod4_3
      specialize h_mod4_3_2 x
      simp [c2] at h_mod4_3_2
      rw [l] at h_mod4_3_2
      apply exists_eq_mul_right_of_dvd at c2

      obtain ⟨t, ht⟩ := c2
      have t1: t ≠ 0 := by omega
      have cases: (4 ∣ y) ∨ (4 ∣ y + 1) ∨ (4 ∣ y + 2) ∨ (4 ∣ y + 3) := by omega
      rcases cases with d1 | d2 | d3 | d4
      -- we need to show 4 ∣y + 1 --
      . replace d1: 2 ∣ y := by
          by_contra! y1
          have y2: 2 ∣ y + 1 := by omega
          have contra: 2 ∣ 1 := by omega
          tauto
        specialize h_even y
        simp [d1] at h_even
        rw [← l] at h_even
        replace ht: x = 4 * t - 1 := by omega
        specialize h3 t
        rw [← ht] at h3
        have w: 2 * f (2 * t - 1) - 1 + 1 = 2 * f (2 * t - 1) := by
          apply Nat.sub_add_cancel
          by_contra! q
          replace q: f (2 * t - 1) = 0 := by omega
          specialize h4 (2 * t - 1)
          have v: 2 * t - 1 ≠ 0 := by
            by_contra! r
            omega
          simp [v] at h4
          tauto
        have x2: 2 ∣ f x + 1 := by
          rw [h3,w]
          apply Nat.dvd_mul_right
        have contra: 2 ∣ 1 := by omega
        tauto
      . apply exists_eq_mul_right_of_dvd at d2
        obtain ⟨s,hs⟩:= d2
        replace d2: y = 4 * s - 1 := by omega
        have h3_1:= h3
        specialize h3 t
        rw [← ht] at h3
        simp at h3
        specialize h3_1 s
        rw [← hs] at h3_1
        simp at h3_1
        replace l: 2 * f (2 * t - 1) - 1 = 2 * f (2 * s - 1) - 1 := by rw [←h3];rw[← h3_1];exact l
        replace l: f (2 * t - 1) = f (2 * s - 1) := by omega
        specialize u (2 * t - 1) (2 * s - 1)
        simp at u
        have t2: 2 * t - 1 < k := by
          by_contra! t2
          have contra: x + 1 ≥ 2 * k + 2 := by
            calc
              x + 1 = 4 * t := by omega
                  _ = 2 * (2 * t - 1) + 2 := by omega
                  _ ≥ 2 * k + 2 := by omega
          nlinarith
        -- similar for s --
        have s2: 2 * s - 1 < k := by
          by_contra! s2
          have contra: y + 1 ≥ 2 * k + 2 := by
            calc
              y + 1 = 4 * s := by omega
                  _ = 2 * (2 * s - 1) + 2 := by omega
                  _ ≥ 2 * k + 2 := by omega
          nlinarith
        simp [t2,s2,l] at u
        omega
      . replace d3: 2 ∣ y := by omega
        specialize h_even y
        simp [d3] at h_even
        have contra: 2 ∣ 1 := by omega
        tauto
      . specialize h_mod4_1 y
        simp [d4] at h_mod4_1
        have contra: 4 ∣ 2 := by omega
        tauto
      -- cases c3: 4 ∣ x + 2, this implies 2 ∣ x --
    . replace c3: 2 ∣ x := by omega
      have c3_1:= c3
      apply exists_eq_mul_right_of_dvd at c3
      obtain ⟨t, ht⟩ := c3
      have h_even_1:= h_even
      specialize h_even x
      simp [c3_1] at h_even
      rw [l] at h_even
      have y1: 2 ∣ y := by
        by_contra! y1
        replace y1: 2 ∣ y + 1 := by omega
        specialize h_odd y
        simp [y1] at h_odd
        have contra: 2 ∣ 1 := by omega
        tauto
      apply exists_eq_mul_right_of_dvd at y1
      obtain ⟨s, hs⟩ := y1
      specialize u t s
      have t2: t < k := by omega
      have s2: s < k := by omega
      simp [t2,s2] at u
      have h1_2:= h1
      specialize h1 t
      specialize h1_2 s
      rw [ht,hs] at l
      rw [h1,h1_2] at l
      replace l: f t = f s := by omega
      simp [l] at u
      omega
     -- cases c4: 4 | x + 3--
    . have h_mod4_1_1:= h_mod4_1
      specialize h_mod4_1_1 x
      simp [c4] at h_mod4_1_1
      rw [l] at h_mod4_1_1
      apply exists_eq_mul_right_of_dvd at c4
      obtain ⟨t, ht⟩ := c4
      have t1: t ≠ 0 := by omega
      have cases: (4 ∣ y) ∨ (4 ∣ y + 1) ∨ (4 ∣ y + 2) ∨ (4 ∣ y + 3) := by omega
      rcases cases with d1 | d2 | d3 | d4
      -- we need to show 4 ∣y + 3 --
      . replace d1: 2 ∣ y := by
          by_contra! y1
          have y2: 2 ∣ y + 1 := by omega
          have contra: 2 ∣ 1 := by omega
          tauto
        specialize h_even y
        simp [d1] at h_even
        rw [← l] at h_even
        replace ht: x = 4 * t - 1 := by omega
        specialize h3 t
        rw [← ht] at h3
        have w: 2 * f (2 * t - 1) - 1 + 1 = 2 * f (2 * t - 1) := by
          apply Nat.sub_add_cancel
          by_contra! q
          replace q: f (2 * t - 1) = 0 := by omega
          specialize h4 (2 * t - 1)
          have v: 2 * t - 1 ≠ 0 := by
            by_contra! r
            omega
          simp [v] at h4
          tauto
        have x2: 2 ∣ f x + 1 := by
          rw [h3,w]
          apply Nat.dvd_mul_right
        have contra: 2 ∣ 1 := by omega
        tauto
      . specialize h_mod4_3 y
        simp [d2] at h_mod4_3
        have contra: 4 ∣ 2 := by omega
        tauto
      . replace d3: 2 ∣ y := by omega
        specialize h_even y
        simp [d3] at h_even
        have contra: 2 ∣ 1 := by omega
        tauto
      . apply exists_eq_mul_right_of_dvd at d4
        obtain ⟨v,hv⟩:= d4
        let s:= v - 1
        let r:= t - 1
        replace d2: y = 4 * s + 1 := by omega
        replace ht: x = 4 * r + 1 := by omega
        have h2_1:= h2
        specialize h2 r
        rw [← ht] at h2
        specialize h2_1 s
        rw [← d2] at h2_1
        replace l: f r = f s := by omega
        specialize u r s
        have r1: r < k := by omega
        have s1: s < k := by omega
        simp [r1,s1,l] at u
        omega
  simp [Function.Injective]
  intro x y
  let N:= x + y
  have ineq: ∀ d : ℕ, d < 2 ^ d * 3 := by
    intro d
    induction' d with d hd
    . norm_num
    . by_cases l: 1 ≤ d
      . calc
          d + 1 ≤  2 * d := by omega
              _ < 2 * (2 ^ d * 3) := by simp [hd]
              _ = 2 ^ (d + 1) * 3 := by ring
      . simp at l
        rw [l]
        norm_num
  have bound_x: x < 2 ^ N * 3 := by
    calc
      x ≤ x + y := by omega
       _= N := by simp [N]
       _< 2 ^ N * 3 := by apply ineq
  have bound_y: y < 2 ^ N * 3 := by
    calc
      y ≤ x + y := by omega
       _= N := by simp [N]
       _< 2 ^ N * 3 := by apply ineq
  -- use key_lemma and inducition to prove the conclusion --
  have f_0: f 0 = 0 := by
    specialize h1 0
    simp at h1
    omega
  have f_1: f 1 = 3 := by
    specialize h2 0
    simp at h2
    omega
  have f_2: f 2 = 6 := by
    specialize h1 1
    simp at h1
    omega
  have f_3: f 3 = 5 := by
    specialize h3 1
    simp at h3
    omega
  have induction_step: ∀ n: ℕ, ∀ x y: ℕ, (x < 2 ^ n * 3) ∧ (y < 2 ^ n * 3) ∧ (f x = f y) → x = y := by
    intro n
    induction' n with n hn
    . intro x y
      simp
      intro j
      intro l
      intro g
      by_contra! s
      have eval: (x = 0) ∧ (y = 1) ∨ (x = 0) ∧ (y = 2) ∨ (x = 1) ∧ (y = 0) ∨ (x = 1) ∧ (y = 2) ∨ (x = 2) ∧ (y = 0) ∨ (x = 2) ∧ (y = 1) := by
        omega
      rcases eval with p1 | p2 | p3 | p4 | p5 | p6
      . simp [p1] at g
        omega
      . simp [p2] at g
        omega
      . simp [p3] at g
        omega
      . simp [p4] at g
        omega
      . simp [p5] at g
        omega
      . simp [p6] at g
        omega
    . let k:= 2 ^ n * 3
      specialize key_lemma (2 ^ n * 3)
      apply key_lemma at hn
      ring_nf
      ring_nf at hn
      exact hn
  specialize induction_step N x y
  tauto