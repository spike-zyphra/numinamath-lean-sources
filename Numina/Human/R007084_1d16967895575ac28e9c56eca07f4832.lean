import Mathlib

open Real
open scoped BigOperators

/- Prove, for all integers a b c d : ℤ, a > 0 → b > 0 → c > 0 → d > 0 →

$$
(2 a-1)(2 b-1)(2 c-1)(2 d-1) \geqslant 2 a b c d-1
$$

and determine the cases of equality. -/
/- Prouver que, pour tous entiers strictement positifs a, b, c, d, on a

$$
(2 a-1)(2 b-1)(2 c-1)(2 d-1) \geqslant 2 a b c d-1
$$

et déterminer les cas d'égalité. -/
theorem inequalities_607477 (a b c d : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (2*a-1)*(2*b-1)*(2*c-1)*(2*d-1) ≥ 2*a*b*c*d-1 ∧
    ((2*a-1)*(2*b-1)*(2*c-1)*(2*d-1) = 2*a*b*c*d-1 ↔ (a = 1 ∧ b = 1 ∧ c = 1) ∨ (a = 1 ∧ c = 1 ∧ d =1) ∨ (b=1∧ c=1∧ d=1)∨ (a=1∧ b=1∧ d=1))  := by
      
      -- A lemma to show the 2 parameters case
      have l (a b:ℤ)(ha : 0<a)(hb : 0<b): (2*a-1)*(2*b-1) ≥ 2*a*b-1 := by
        have h2: (2*a-1)*(2*b-1) - (2*a*b-1) ≥ 0 := by
          have h3: (2*a-1)*(2*b-1) - (2*a*b-1) = 2* (a*b - a - b + 1) := by
            ring_nf
          rw [h3]
          have h4: a*b - a - b + 1 ≥ 0 := by
            have ha': a-1≥ 0 := by linarith
            have hb': b-1≥ 0 := by linarith
            have h': a*b - a - b + 1 = (a - 1)*(b - 1) := by ring
            rw [h']
            exact mul_nonneg ha' hb'
          linarith
        linarith

      constructor
      -- Apply lemma l to the 2 groups of paras, a,b and c,d
      have h1: (2*a-1)*(2*b-1) ≥ 2*a*b-1 := by
        apply l a b ha hb
      have h2: (2*c-1)*(2*d-1) ≥ 2*c*d-1 := by
        apply l c d hc hd
      -- Apply lemma l to new paras a*b and c*d
      have h3': (2*(a*b) - 1)*(2*(c*d) - 1) ≥ 2*(a*b)*(c*d) - 1 := by
        apply l (a*b) (c*d) _ _
        linarith
        linarith

      -- Combine the h1, h2, h3'.
      have h4: ((2*a-1)*(2*b-1))*((2*c-1)*(2*d-1)) ≥ (2*a*b - 1)*((2*c-1)*(2*d-1)) := by
        have h1: (2*c-1)*(2*d-1) ≥ 0 := by linarith
        apply mul_le_mul_of_nonneg_right _ _
        linarith
        exact h1
      have h5: (2*a*b - 1)*((2*c-1)*(2*d-1)) ≥ (2*a*b - 1)*(2*c*d-1) := by
        have h1: 2*a*b - 1 ≥ 0 := by linarith
        apply mul_le_mul_of_nonneg_left _ _
        linarith
        exact h1
      linarith
      

      -- A lemma to show if a*b=1 with a≥1,b≥1, then a=b=1.
      have l11 (a b:ℤ) (h11: a*b=1) (ha: a>0)(hb:b>0): a =1 ∧ b=1 := by
        have hb1: b-1≥ 0 := by linarith
        have ha1: 1-a≤ 0 := by linarith
        have h1 : (1-a)*(b-1) ≥ 0 := by
          ring_nf
          rw [h11]
          ring_nf
          linarith
        have h1' : (b-1)*(1-a) ≤  0 := by
          apply mul_nonpos_of_nonneg_of_nonpos
          linarith
          linarith
        have h1'': (b-1)*(1-a) = 0 := by
          linarith
        rw [mul_eq_zero] at h1''
        rcases h1'' with h1|h2
        have h1_1: b=1 := by linarith
        rw [h1_1] at h11
        have ha_1: a=1 := by linarith
        tauto
        have h1_1: a=1 := by linarith
        rw [h1_1] at h11
        have ha_1: b=1 := by linarith
        tauto
      
      -- A lemma to show that the eq case for 2 paras
      have leq (a b:ℤ)(ha : 0<a)(hb : 0<b): (2*a-1)*(2*b-1) = 2*a*b-1 ↔ (a = 1) ∨ (b = 1):= by
        constructor
        intro hAB
        have eq: (2*a-1)*(2*b-1) - (2*a*b - 1) = 2* (a*b - a - b + 1) := by ring_nf
        have eq': 2* (a*b - a - b + 1) = 2*(a-1)*(b-1) := by ring
        rw [eq', hAB] at eq
        have eq'': (a-1)*(b-1) = 0 := by linarith
        have aeq0: a-1 = 0 ∨ b-1 = 0 := by
         apply mul_eq_zero.mp
         exact eq''
        rcases aeq0 with aaeq0 | beq0
        have _: a = 1 := by linarith
        tauto
        have _: b = 1 := by linarith
        tauto
        intro hab
        rcases hab with h | h
        rw[h]
        ring
        rw[h]
        ring

      constructor
      intro heq1

      have heq: (2*a*b - 1)*(2*c*d-1) = 2*a*b*c*d - 1 := by
        have h1: (2*a-1)*(2*b-1) ≥ 2*a*b-1 := by
          apply l a b ha hb
        have h2: (2*c-1)*(2*d-1) ≥ 2*c*d-1 := by
          apply l c d hc hd
        have h3': (2*(a*b) - 1)*(2*(c*d) - 1) ≥ 2*(a*b)*(c*d) - 1 := by
          apply l (a*b) (c*d) _ _
          linarith
          linarith

        have h4: ((2*a-1)*(2*b-1))*((2*c-1)*(2*d-1)) ≥ (2*a*b - 1)*((2*c-1)*(2*d-1)) := by
          have h1: (2*c-1)*(2*d-1) ≥ 0 := by linarith
          apply mul_le_mul_of_nonneg_right _ _
          linarith
          exact h1
        have h5: (2*a*b - 1)*((2*c-1)*(2*d-1)) ≥ (2*a*b - 1)*(2*c*d-1) := by
          have h1: 2*a*b - 1 ≥ 0 := by linarith
          apply mul_le_mul_of_nonneg_left _ _
          linarith
          exact h1
        have h6: (2*a*b - 1)*(2*c*d-1) ≥ 2*a*b*c*d - 1 := by
          linarith
        have h7: ((2*a-1)*(2*b-1))*((2*c-1)*(2*d-1)) ≥ (2*a*b - 1)*(2*c*d-1) := by
          linarith
        have h7': (2*a-1)*(2*b-1)*(2*c-1)*(2*d-1) ≥ (2*a*b - 1)*(2*c*d-1):= by
          linarith
        linarith
      have h1': (2*(a*b)-1)*(2*(c*d)-1) = 2*(a*b)*(c*d)-1 := by
        linarith
      have h1'': a*b=1 ∨ c*d = 1 := by
        have ha:a*b> 0:=by
          apply mul_pos
          linarith
          linarith
        have hb: c*d > 0 := by
          apply mul_pos
          linarith
          linarith
        rw [leq _ _ ha hb] at h1'
        exact h1'
      have h1''': a = 1 ∧ b = 1 ∨ c = 1 ∧ d = 1 := by
        rcases h1'' with ha' | hb'
        left
        apply l11 _ _
        exact ha'
        linarith
        linarith
        right
        apply l11 _ _
        exact hb'
        linarith
        linarith

      rcases h1''' with hab | hcd
      rw [hab.left, hab.right] at heq1
      have hcd': (2*c-1)*(2*d-1)=2*c*d-1 := by
        linarith
      have l': c=1 ∨ d=1 := by
        rw [leq] at hcd'
        exact hcd'
        exact hc
        exact hd
      tauto

      rw [hcd.left, hcd.right] at heq1
      have heq1' : (2*a-1)*(2*b-1) = 2*a*b-1 := by
        linarith
      rw [leq] at heq1'
      tauto
      linarith
      linarith

      intro hw
      rcases hw with h0|h1|h2|h3
      rw [h0.left, h0.right.left, h0.right.right]
      linarith
      rw [h1.left, h1.right.left, h1.right.right]
      linarith
      rw [h2.left, h2.right.left, h2.right.right]
      linarith
      rw [h3.left, h3.right.left, h3.right.right]
      linarith


