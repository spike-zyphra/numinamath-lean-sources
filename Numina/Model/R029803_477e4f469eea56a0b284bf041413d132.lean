import Mathlib


open Finset Real


lemma lemma_1 (x : ℝ) (b : ℝ) (h₀ : 0 < x) (h₁ : 0 < b) (h₂ : b ≠ 1) :
    x ^ logb b x = b ^ (logb b x) ^ 2 := by
  have hx : x = (b ^ (logb b x) ) := by
    rw [Real.rpow_logb]
    all_goals
      try tauto
      all_goals
        try linarith
  have h4 : x ^ logb b x = (b ^ (logb b x) ) ^ logb b x := by
    rw [hx]
    all_goals
      try tauto
      all_goals
        try nlinarith
        all_goals
          try try positivity
  rw [h4]
  have h5 : ((b ^ (logb b x) ) ^ logb b x) = (b ^ ((logb b x) ^2) ) := by
    calc
      ((b ^ (logb b x) ) ^ logb b x) = (b ^ ((logb b x) * (logb b x) ) ) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals try positivity
        all_goals
          try nlinarith
          all_goals
            try tauto
      _ = (b ^ ((logb b x) ^2) ) := by
        ring_nf
  exact h5
  all_goals
    try positivity
    all_goals
      try nlinarith <;> try tauto
  all_goals
    try tauto
    all_goals
      try nlinarith


theorem algebra_96474 {S : Set ℝ} [Fintype S]
    (hS : S = { x | 0 < x ∧ √1995 * x ^ (logb 1995 x) = x ^ 2}) :
    ⌊(∏ x ∈ S, x)⌋₊ % 1000 = 25 := by
  have h1995 : (1995 : ℝ) ^ 2 = 3980025 := by norm_num
  have hS_eq : S = { (1995 : ℝ) ^ (1 + Real.sqrt 2 / 2 : ℝ), (1995 : ℝ) ^ (1 - Real.sqrt 2 / 2 : ℝ) } := by
    rw [hS]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- First direction: if x is a solution then x is one of the roots
      intro h
      rcases h with ⟨hx_pos, heq⟩
      have h1 : √1995 * x ^ (logb 1995 x) = x ^ 2 := heq
      have h2 : logb 1995 (√1995 * x ^ (logb 1995 x)) = logb 1995 (x ^ 2) := by
        rw [h1]
      have h3 : logb 1995 (√1995 * x ^ (logb 1995 x)) = logb 1995 (√1995) + logb 1995 (x ^ (logb 1995 x) ) := by
        rw [logb_mul (by positivity) (by positivity)]
      have h4 : logb 1995 (√1995) = (1 / 2 : ℝ) := by 
        calc
          logb 1995 (√1995) = logb 1995 (1995 ^ (1 / 2 : ℝ) ) := by
            rw [Real.sqrt_eq_rpow]
            all_goals norm_num
          _ = (1 / 2 : ℝ) := by
            rw [logb_rpow]
            all_goals norm_num
      have h5 : logb 1995 (x ^ (logb 1995 x) ) = (logb 1995 x) ^ 2 := by
        rw [logb_rpow_eq_mul_logb_of_pos]
        <;> try simp at *
        all_goals
          try nlinarith
          all_goals
            try tauto
            all_goals
              try positivity
      have h6 : logb 1995 (x ^ 2) = (2 : ℝ) * logb 1995 x := by
        simp [logb_pow]
        all_goals norm_num
      rw [h3, h4, h5, h6] at h2
      have h7 : (logb 1995 x) ^ 2 - 2 * logb 1995 x + 1 / 2 = 0 := by
        nlinarith
      have h8 : (logb 1995 x - (1 - Real.sqrt 2 / 2)) * (logb 1995 x - (1 + Real.sqrt 2 / 2)) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0: ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), h7]
      cases' (mul_eq_zero.1 h8) with h9 h10
      · -- First case: $\log_{1995}x = 1 - \frac{\sqrt{2}}{2}$.
        have h11 : logb 1995 x = (1 - Real.sqrt 2 / 2 : ℝ) := by
          linarith
        have hx1995 : x = (1995 : ℝ) ^ logb 1995 x := by
          field_simp
          all_goals
            try tauto
            all_goals
              try positivity
        rw [h11] at hx1995
        right
        tauto
      · -- Second case: $\log_{1995}x = 1 + \frac{\sqrt{2}}{2}$.
        have h11 : logb 1995 x = (1 + Real.sqrt 2 / 2 : ℝ) := by
          linarith
        have hx1995 : x = (1995 : ℝ) ^ logb 1995 x := by
          field_simp
          all_goals
            try tauto
            all_goals
              try positivity
        rw [h11] at hx1995
        left
        tauto
    · -- Second direction: if x is one of the roots then it's a solution
      rintro (rfl | rfl)
      · -- First root
        constructor
        · -- Show it's positive
          positivity
        · -- Show it satisfies the equation
          have h19951 : logb 1995 ((1995 : ℝ) ^ (1 + Real.sqrt 2 / 2 : ℝ) ) = (1 + Real.sqrt 2 / 2 : ℝ) := by
            rw [logb_rpow]
            all_goals norm_num
          -- Substituting into the equation
          have h_eq1 : √1995 * ((1995 : ℝ) ^ (1 + Real.sqrt 2 / 2 : ℝ) ) ^ (logb 1995 ((1995 : ℝ) ^ (1 + Real.sqrt 2 / 2 : ℝ) ) ) = ((1995 : ℝ) ^ (1 + Real.sqrt 2 / 2 : ℝ) ) ^ 2 := by
            rw [h19951]
            have h19952 : √1995 = (1995 : ℝ) ^ (1 / 2 : ℝ) := by
              rw [Real.sqrt_eq_rpow]
              all_goals norm_num
            rw [h19952]
            have h19953 : ((1995 : ℝ) ^ (1 / 2 : ℝ) ) * ((1995 : ℝ) ^ (1 + Real.sqrt 2 / 2 : ℝ) ) ^ (1 + Real.sqrt 2 / 2 : ℝ) = ((1995 : ℝ) ^ (1 + Real.sqrt 2 / 2 : ℝ) ) ^ 2 := by
              have h19954 : ((1995 : ℝ) ^ (1 / 2 : ℝ) ) * ((1995 : ℝ) ^ (1 + Real.sqrt 2 / 2 : ℝ) ) ^ (1 + Real.sqrt 2 / 2 : ℝ) = (1995 : ℝ) ^ (1 / 2 + (1 + Real.sqrt 2 / 2) ^ 2 : ℝ) := by
                calc
                  ((1995 : ℝ) ^ (1 / 2 : ℝ) ) * ((1995 : ℝ) ^ (1 + Real.sqrt 2 / 2 : ℝ) ) ^ (1 + Real.sqrt 2 / 2 : ℝ) = (1995 : ℝ) ^ (1 / 2 : ℝ) * (1995 : ℝ) ^ ((1 + Real.sqrt 2 / 2) * (1 + Real.sqrt 2 / 2) : ℝ) := by
                    rw [← Real.rpow_mul]
                    ring_nf
                    all_goals try positivity
                    all_goals
                      try nlinarith
                      all_goals
                        try tauto
                  _ = (1995 : ℝ) ^ (1 / 2 + ((1 + Real.sqrt 2 / 2) * (1 + Real.sqrt 2 / 2) ) : ℝ) := by
                    rw [← Real.rpow_add]
                    ring_nf
                    all_goals try positivity
                    all_goals
                      try nlinarith
                      all_goals
                        try tauto
                  _ = (1995 : ℝ) ^ (1 / 2 + (1 + Real.sqrt 2 / 2) ^ 2 : ℝ) := by
                    ring
              have h19955 : ((1995 : ℝ) ^ (1 + Real.sqrt 2 / 2 : ℝ) ) ^ 2 = (1995 : ℝ) ^ (2 * (1 + Real.sqrt 2 / 2) : ℝ) := by
                calc
                  ((1995 : ℝ) ^ (1 + Real.sqrt 2 / 2 : ℝ) ) ^ 2 = (1995 : ℝ) ^ ((2 : ℝ) * (1 + Real.sqrt 2 / 2) ) := by
                    rw [← Real.rpow_natCast, ← Real.rpow_mul]
                    ring_nf
                    all_goals try positivity
                    all_goals
                      try nlinarith
                      all_goals
                        try tauto
                  _ = (1995 : ℝ) ^ (2 * (1 + Real.sqrt 2 / 2) : ℝ) := by
                    ring_nf
              rw [h19954, h19955]
              have h19956 : 1 / 2 + (1 + Real.sqrt 2 / 2) ^ 2 = 2 * (1 + Real.sqrt 2 / 2) := by
                nlinarith [Real.sqrt_pos.mpr (show (0: ℝ) < 2 by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
              rw [h19956]
            exact h19953
          exact h_eq1
      · -- Second root
        constructor
        · -- Show it's positive
          positivity
        · -- Show it satisfies the equation
          have h19951 : logb 1995 ((1995 : ℝ) ^ (1 - Real.sqrt 2 / 2 : ℝ) ) = (1 - Real.sqrt 2 / 2 : ℝ) := by
            rw [logb_rpow]
            all_goals norm_num
          -- Substituting into the equation
          have h_eq1 : √1995 * ((1995 : ℝ) ^ (1 - Real.sqrt 2 / 2 : ℝ) ) ^ (logb 1995 ((1995 : ℝ) ^ (1 - Real.sqrt 2 / 2 : ℝ) ) ) = ((1995 : ℝ) ^ (1 - Real.sqrt 2 / 2 : ℝ) ) ^ 2 := by
            rw [h19951]
            have h19952 : √1995 = (1995 : ℝ) ^ (1 / 2 : ℝ) := by
              rw [Real.sqrt_eq_rpow]
              all_goals norm_num
            rw [h19952]
            have h19953 : ((1995 : ℝ) ^ (1 / 2 : ℝ) ) * ((1995 : ℝ) ^ (1 - Real.sqrt 2 / 2 : ℝ) ) ^ (1 - Real.sqrt 2 / 2 : ℝ) = ((1995 : ℝ) ^ (1 - Real.sqrt 2 / 2 : ℝ) ) ^ 2 := by
              have h19954 : ((1995 : ℝ) ^ (1 / 2 : ℝ) ) * ((1995 : ℝ) ^ (1 - Real.sqrt 2 / 2 : ℝ) ) ^ (1 - Real.sqrt 2 / 2 : ℝ) = (1995 : ℝ) ^ (1 / 2 + (1 - Real.sqrt 2 / 2) ^ 2 : ℝ) := by
                calc
                  ((1995 : ℝ) ^ (1 / 2 : ℝ) ) * ((1995 : ℝ) ^ (1 - Real.sqrt 2 / 2 : ℝ) ) ^ (1 - Real.sqrt 2 / 2 : ℝ) = (1995 : ℝ) ^ (1 / 2 : ℝ) * (1995 : ℝ) ^ ((1 - Real.sqrt 2 / 2) * (1 - Real.sqrt 2 / 2) : ℝ) := by
                    rw [← Real.rpow_mul]
                    ring_nf
                    all_goals try positivity
                    all_goals
                      try nlinarith
                      all_goals
                        try tauto
                  _ = (1995 : ℝ) ^ (1 / 2 + ((1 - Real.sqrt 2 / 2) * (1 - Real.sqrt 2 / 2) ) : ℝ) := by
                    rw [← Real.rpow_add]
                    ring_nf
                    all_goals try positivity
                    all_goals
                      try nlinarith
                      all_goals
                        try tauto
                  _ = (1995 : ℝ) ^ (1 / 2 + (1 - Real.sqrt 2 / 2) ^ 2 : ℝ) := by
                    ring
              have h19955 : ((1995 : ℝ) ^ (1 - Real.sqrt 2 / 2 : ℝ) ) ^ 2 = (1995 : ℝ) ^ (2 * (1 - Real.sqrt 2 / 2) : ℝ) := by
                calc
                  ((1995 : ℝ) ^ (1 - Real.sqrt 2 / 2 : ℝ) ) ^ 2 = (1995 : ℝ) ^ ((2 : ℝ) * (1 - Real.sqrt 2 / 2) ) := by
                    rw [← Real.rpow_natCast, ← Real.rpow_mul]
                    ring_nf
                    all_goals try positivity
                    all_goals
                      try nlinarith
                      all_goals
                        try tauto
                  _ = (1995 : ℝ) ^ (2 * (1 - Real.sqrt 2 / 2) : ℝ) := by
                    ring_nf
              rw [h19954, h19955]
              have h19956 : 1 / 2 + (1 - Real.sqrt 2 / 2) ^ 2 = 2 * (1 - Real.sqrt 2 / 2) := by
                nlinarith [Real.sqrt_pos.mpr (show (0: ℝ) < 2 by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
              rw [h19956]
            exact h19953
          exact h_eq1
  have h19952 : ((1995 : ℝ) ^ (1 + Real.sqrt 2 / 2 : ℝ) ) * ((1995 : ℝ) ^ (1 - Real.sqrt 2 / 2 : ℝ) ) = (1995 : ℝ) ^ 2 := by
    calc
      _ = (1995 : ℝ) ^ ((1 + Real.sqrt 2 / 2 : ℝ) + (1 - Real.sqrt 2 / 2 : ℝ) ) := by
        rw [← Real.rpow_add]
        ring_nf
        all_goals norm_num
      _ = (1995 : ℝ) ^ (2 : ℝ) := by
        norm_num
        <;> ring_nf
      _ = (1995 : ℝ) ^ 2 := by
        norm_cast
  -- Show the product over the finset equals 1995^2
  have h9 : (∏ x ∈ (S : Set ℝ).toFinset, x) = ((1995 : ℝ) ^ 2 : ℝ) := by
    have h_eq4 : (S : Set ℝ) = { (1995 : ℝ) ^ (1 + Real.sqrt 2 / 2 : ℝ), (1995 : ℝ) ^ (1 - Real.sqrt 2 / 2 : ℝ) } := hS_eq
    have eq2 : (S : Set ℝ).toFinset = ({ (1995 : ℝ) ^ (1 + Real.sqrt 2 / 2 : ℝ), (1995 : ℝ) ^ (1 - Real.sqrt 2 / 2 : ℝ) } : Set ℝ).toFinset := by
      simp [h_eq4]
      <;> try try native_decide 
    rw [eq2]
    have h10 : ( (1995 : ℝ) ^ (1 + Real.sqrt 2 / 2 : ℝ) ) ≠ ( (1995 : ℝ) ^ (1 - Real.sqrt 2 / 2 : ℝ) ) := by
      by_contra h_eq
      have h11 : (1 + Real.sqrt 2 / 2 : ℝ) = (1 - Real.sqrt 2 / 2 : ℝ) := by
        have h12 : (1995 : ℝ) ^ (1 + Real.sqrt 2 / 2 : ℝ) = (1995 : ℝ) ^ (1 - Real.sqrt 2 / 2 : ℝ) := by 
          exact_mod_cast h_eq
        have h13 : (1 + Real.sqrt 2 / 2 : ℝ) = (1 - Real.sqrt 2 / 2 : ℝ) := by
          apply_fun (Real.logb (1995 : ℝ)) at h12
          -- Simplify equations
          have h41 : Real.logb (1995 : ℝ) ((1995 : ℝ) ^ (1 + Real.sqrt 2 / 2 : ℝ) ) = (1 + Real.sqrt 2 / 2 : ℝ) := by
            rw [logb_rpow]
            all_goals norm_num
          have h42 : Real.logb (1995 : ℝ) ((1995 : ℝ) ^ (1 - Real.sqrt 2 / 2 : ℝ) ) = (1 - Real.sqrt 2 / 2 : ℝ) := by
            rw [logb_rpow]
            all_goals norm_num
          nlinarith 
        exact_mod_cast h13
      nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    simp [prod_pair h10, h19952]
    <;> norm_num
    <;> try try native_decide
    all_goals
      try norm_num 
      <;> tauto 
      all_goals
        try nlinarith
        all_goals
          try try native_decide
  rw [h9]
  norm_num [h1995]
  <;> norm_num [h1995] <;> try try native_decide <;> try tauto