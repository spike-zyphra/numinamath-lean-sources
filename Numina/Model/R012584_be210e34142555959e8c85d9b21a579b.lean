import Mathlib

theorem number_theory_311657 (a b c : ℤ) (h : a^2 + b^4 + c^6 ≤ Real.sqrt 5) :
    (-2 : ℝ)^a + (-2)^b + (-2)^c = 3 ∨ (-2 : ℝ)^a + (-2)^b + (-2)^c = -3 ∨
    (-2 : ℝ)^a + (-2)^b + (-2)^c = 0 ∨ (-2 : ℝ)^a + (-2)^b + (-2)^c = 3 / 2 ∨
    (-2 : ℝ)^a + (-2)^b + (-2)^c = -3 / 2 := by
  have h1 : a^2 + b^4 + c^6 ≤ 2 := by 
    by_contra h2
    push_neg at h2
    have h2' : a^2 + b^4 + c^6 ≥ 3 := by
      omega
    have h2'' : (a^2 + b^4 + c^6 : ℝ) ≥ (3 : ℝ) := by exact_mod_cast h2'
    have h4 : (a^2 + b^4 + c^6 : ℝ) ≤ (Real.sqrt 5 : ℝ) := by
      simpa using h
    have h5 : (3 : ℝ) ≤ (Real.sqrt 5 : ℝ) := by
      nlinarith
    have h10 : (Real.sqrt 5 : ℝ) ^ 2 = (5 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg ((Real.sqrt 5) : ℝ)]
  have h2 : a^2 ≤ 2 := by 
    nlinarith [sq_nonneg (b ^ 2), sq_nonneg (c ^ 3), sq_nonneg (a ^ 2 - 2 : ℤ), sq_nonneg (b ^ 2 - 1 : ℤ), sq_nonneg (c ^ 3 - 1 : ℤ), 
      sq_nonneg ((a : ℤ)), sq_nonneg ((b : ℤ)), sq_nonneg ((c : ℤ)), 
      show b ^ 4 ≥ 0 from by positivity, 
      show c ^ 6 ≥ 0 from by positivity
    ]
  have h3 : b^4 ≤ 2 := by
    nlinarith [sq_nonneg (a ^ 2 - 1 : ℤ), sq_nonneg (c ^ 3 - 1 : ℤ), 
      sq_nonneg ((a : ℤ)), sq_nonneg ((b : ℤ)), sq_nonneg ((c : ℤ)),
      show a ^ 2 ≥ 0 from by positivity,
      show c ^ 6 ≥ 0 from by positivity
    ]
  have h4 : c^6 ≤ 2 := by
    nlinarith [sq_nonneg (a ^ 2 - 1 : ℤ), sq_nonneg (b ^ 2 - 1 : ℤ), 
      sq_nonneg ((a : ℤ)), sq_nonneg ((b : ℤ)), sq_nonneg ((c : ℤ)),
      show a ^ 2 ≥ 0 from by positivity,
      show b ^ 4 ≥ 0 from by positivity
    ]
  have ha1 : a ≤ 1 := by
    nlinarith [sq_nonneg ((a : ℤ)), sq_nonneg ((a^2 - 2 : ℤ)), h2,
      sq_nonneg ((b : ℤ)), sq_nonneg ((c : ℤ)),
      show 0 ≤ (b ^ 2: ℤ) by positivity,
      show 0 ≤ (c ^ 2: ℤ) by positivity 
    ]
  have ha2 : a ≥ -1 := by
    nlinarith [sq_nonneg ((a : ℤ)), sq_nonneg ((a^2 - 2 : ℤ)), h2,
      sq_nonneg ((b : ℤ)), sq_nonneg ((c : ℤ)),
      show 0 ≤ (b ^ 2: ℤ) by positivity,
      show 0 ≤ (c ^ 2: ℤ) by positivity 
    ]
  have hb1 : b ≤ 1 := by
    have hb4 : b^4 ≤ 2 := h3
    have h52 : b ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg ((b ^ 2 - 1: ℤ)), sq_nonneg ((b : ℤ)), sq_nonneg ((b ^ 2 : ℤ)), 
        sq_nonneg ((b^4 - 2 : ℤ)), sq_nonneg ((b : ℤ)), 
          sq_nonneg ((b ^ 2 : ℤ)), 
            show 0 ≤ (b : ℤ) ^ 2 from by positivity, 
              sq_nonneg ((b^2 - 1 : ℤ)), sq_nonneg ((b : ℤ))
      ]
    have h53 : b ≤ 1 := by
      nlinarith [sq_nonneg ((b ^ 2 - 1 : ℤ)), sq_nonneg ((b ^ 2 : ℤ)), sq_nonneg ((b : ℤ)), 
        h52, 
          sq_nonneg ((b + 1 : ℤ)), sq_nonneg ((b - 1 : ℤ))
      ]
    exact_mod_cast h53
  have hb2 : b ≥ -1 := by
    have hb4 : b^4 ≤ 2 := h3
    have h51 : b ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg ((b ^ 2 - 1: ℤ)), sq_nonneg ((b : ℤ)), sq_nonneg ((b ^ 2 : ℤ)), 
        sq_nonneg ((b^4 - 2 : ℤ)), sq_nonneg ((b : ℤ)), 
          sq_nonneg ((b ^ 2 : ℤ)), 
            show 0 ≤ (b : ℤ) ^ 2 from by positivity, 
              sq_nonneg ((b^2 - 1 : ℤ)), sq_nonneg ((b : ℤ))
      ]
    have h50 : b ≥ -1 := by
      nlinarith [sq_nonneg ((b ^ 2 - 1 : ℤ)), sq_nonneg ((b ^ 2 : ℤ)), sq_nonneg ((b : ℤ)), 
        h51, 
          sq_nonneg ((b + 1 : ℤ)), sq_nonneg ((b - 1 : ℤ))
      ]
    exact_mod_cast h50
  have hc1 : c ≤ 1 := by
    have hc6 : c^6 ≤ 2 := h4
    have hc41 : c ^ 2 ≤ 1 := by 
      nlinarith [sq_nonneg ((c : ℤ)), sq_nonneg ((c ^ 2 - 1 : ℤ)), sq_nonneg ((c ^ 6 - 2: ℤ)), 
          sq_nonneg ((c: ℤ)), 
          sq_nonneg ((c ^ 2: ℤ)), 
            sq_nonneg ((c ^ 6: ℤ)), 
              show 0 ≤ (c : ℤ)^2 by positivity, 
                sq_nonneg ((c^2 - 1: ℤ)), sq_nonneg ((c: ℤ))
      ]
    have hc42 : c ≤ 1 := by
      nlinarith [sq_nonneg ((c ^ 2 - 1 : ℤ)), sq_nonneg ((c ^ 2 : ℤ)), sq_nonneg ((c : ℤ)), 
        hc41, 
          sq_nonneg ((c + 1 : ℤ)), sq_nonneg ((c - 1 : ℤ))
      ]
    exact_mod_cast hc42
  have hc2 : c ≥ -1 := by
    have hc6 : c^6 ≤ 2 := h4
    have hc41 : c ^ 2 ≤ 1 := by 
      nlinarith [sq_nonneg ((c : ℤ)), sq_nonneg ((c ^ 2 - 1 : ℤ)), sq_nonneg ((c ^ 6 - 2: ℤ)), 
          sq_nonneg ((c: ℤ)), 
          sq_nonneg ((c ^ 2: ℤ)), 
            sq_nonneg ((c ^ 6: ℤ)), 
              show 0 ≤ (c : ℤ)^2 by positivity, 
                sq_nonneg ((c^2 - 1: ℤ)), sq_nonneg ((c: ℤ))
      ]
    have hc40 : c ≥ -1 := by
      nlinarith [sq_nonneg ((c ^ 2 - 1 : ℤ)), sq_nonneg ((c ^ 2 : ℤ)), sq_nonneg ((c : ℤ)), 
        hc41, 
          sq_nonneg ((c + 1 : ℤ)), sq_nonneg ((c - 1 : ℤ))
      ]
    exact_mod_cast hc40
  interval_cases a <;> interval_cases b <;> interval_cases c
    <;> norm_num [Real.sqrt_nonneg, Real.sq_sqrt, pow_succ, pow_zero] at h ⊢ <;> tauto