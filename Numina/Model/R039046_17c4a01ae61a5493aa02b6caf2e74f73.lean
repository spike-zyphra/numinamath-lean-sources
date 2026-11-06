import Mathlib
set_option maxRecDepth 5000

open Finset

theorem inequalities_605266 {r : ℕ → ℝ} (hsum : ∑ i ∈ range 2019, r i = 0)
(hsumsq : ∑ i ∈ range 2019, r i ^ 2 = 1) :
let a := (image r (range 2019)).min' (by use r 0; simp; use 0; simp);
let b := (image r (range 2019)).max' (by use r 0; simp; use 0; simp); a * b ≤ -1 / 2019 := by
  intro a b
  have h2 : ∀ i ∈ range 2019, a ≤ r i := by 
    intro i hi
    have h3 : r i ∈ image r (range 2019) := by 
      simp [Finset.mem_image]
      use i
      all_goals simp at *
      <;> try { tauto }
    have h4 : a ≤ r i := by
      apply Finset.min'_le 
      all_goals
      try { 
        simp_all [Finset.mem_image]
        all_goals try { 
          tauto 
        }
        all_goals try { 
          aesop 
        }
      }
      all_goals try { 
        aesop 
        <;> norm_num 
        <;> try { tauto } 
      }
    linarith
  have h12 : ∀ i ∈ range 2019, r i ≤ b := by 
    intro i hi
    have h3 : r i ∈ image r (range 2019) := by 
      simp [Finset.mem_image]
      use i
      all_goals simp at *
      <;> try { tauto }
    have h4 : r i ≤ b := by
      apply Finset.le_max' 
      all_goals 
      try { 
        simp_all [Finset.mem_image]
        all_goals try { 
          tauto 
        }
        all_goals try { 
          aesop 
        }
      }
      all_goals try { 
        aesop 
        <;> norm_num 
        <;> try { tauto } 
      }
    linarith
  have h3 : ∑ i in range 2019, (r i - a) * (b - r i) ≥ 0 := by
    have h4 : ∀ i ∈ range 2019, (r i - a) * (b - r i) ≥ 0 := by 
      intro i hi
      have h5 : a ≤ r i := h2 i hi
      have h6 : r i ≤ b := h12 i hi
      nlinarith 
    have h7 : ∑ i in range 2019, (r i - a) * (b - r i) ≥ 0 := by 
      apply Finset.sum_nonneg 
      intro i hi 
      apply h4 i hi 
    linarith
  have h8 : ∑ i in range 2019, (r i - a) * (b - r i) = -1 - (2019 : ℝ) * (a * b) := by 
    have h9 : ∑ i in range 2019, (r i - a) * (b - r i) = ∑ i in range 2019, ((b * r i - r i ^ 2 - a * b + a * r i) ) := by 
      congr 
      funext i
      ring 
    rw [h9]
    have h10 : ∑ i in range 2019, ((b * r i - r i ^ 2 - a * b + a * r i) ) = 
        b * (∑ i in range 2019, r i) - (∑ i in range 2019, r i ^ 2) - 2019 * (a * b) + a * (∑ i in range 2019, r i) := by 
      simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      <;> ring 
      <;> try { 
        simp [mul_add, mul_assoc] 
        <;> try { 
          ring 
        } 
        <;> try { 
          norm_num 
        }
        all_goals try { 
          tauto 
        }
      }
    rw [h10]
    rw [hsum] at *
    rw [hsumsq] at *
    all_goals
    try { 
      norm_num 
      <;> nlinarith 
      all_goals try { 
        try { 
          nlinarith 
        }
      }
    }
    <;> try { 
      try { 
        nlinarith 
      }
    }
    all_goals try { 
      norm_num
    }
    all_goals try { 
      try { 
        nlinarith 
      }
    }
  linarith [h3, h8]
  all_goals try { 
    nlinarith 
    all_goals try { 
      norm_num 
    }
    all_goals try { 
      tauto 
    }
  }
  all_goals try { 
    try { 
      tauto 
    }
  }