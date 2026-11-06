import Mathlib

theorem number_theory_604099 {f : ℕ → ℕ} (hf1 : ∀ n, 0 < n → f (f n) = 4 * n + 9)
    (hf2 : ∀ k, f (2 ^ k) = 2 ^ (k + 1) + 3) :
    f 1789 = 3581 := by

  have h1 : f 1 = 5 := by
    specialize hf2 0
    norm_num at hf2 ⊢
    exact hf2

  have h5 : f 5 = 13 := by
    have h1' : f 1 = 5 := h1
    specialize hf1 1 (by norm_num)
    rw [h1'] at hf1
    norm_num at hf1 ⊢
    exact hf1

  have h13 : f 13 = 29 := by
    have h5' : f 5 = 13 := h5
    specialize hf1 5 (by norm_num)
    rw [h5'] at hf1
    norm_num at hf1 ⊢
    exact hf1

  have h29 : f 29 = 61 := by
    have h13' : f 13 = 29 := h13
    specialize hf1 13 (by norm_num)
    rw [h13'] at hf1
    norm_num at hf1 ⊢
    exact hf1

  have h61 : f 61 = 125 := by
    have h29' : f 29 = 61 := h29
    specialize hf1 29 (by norm_num)
    rw [h29'] at hf1
    norm_num at hf1 ⊢
    exact hf1

  have h125 : f 125 = 253 := by
    have h61' : f 61 = 125 := h61
    specialize hf1 61 (by norm_num)
    rw [h61'] at hf1
    norm_num at hf1 ⊢
    exact hf1

  have h253 : f 253 = 509 := by
    have h125' : f 125 = 253 := h125
    specialize hf1 125 (by norm_num)
    rw [h125'] at hf1
    norm_num at hf1 ⊢
    exact hf1

  have h509 : f 509 = 1021 := by
    have h253' : f 253 = 509 := h253
    specialize hf1 253 (by norm_num)
    rw [h253'] at hf1
    norm_num at hf1 ⊢
    exact hf1

  have h1021 : f 1021 = 2045 := by
    have h509' : f 509 = 1021 := h509
    specialize hf1 509 (by norm_num)
    rw [h509'] at hf1
    norm_num at hf1 ⊢
    exact hf1

  have h4 : f 4 = 11 := by
    specialize hf2 2
    norm_num at hf2 ⊢
    exact hf2

  have h11 : f 11 = 25 := by
    have h4' : f 4 = 11 := h4
    specialize hf1 4 (by norm_num)
    rw [h4'] at hf1
    norm_num at hf1 ⊢
    exact hf1

  have h25 : f 25 = 53 := by
    have h11' : f 11 = 25 := h11
    specialize hf1 11 (by norm_num)
    rw [h11'] at hf1
    norm_num at hf1 ⊢
    exact hf1

  have h53 : f 53 = 109 := by
    have h25' : f 25 = 53 := h25
    specialize hf1 25 (by norm_num)
    rw [h25'] at hf1
    norm_num at hf1 ⊢
    exact hf1

  have h109 : f 109 = 221 := by
    have h53' : f 53 = 109 := h53
    specialize hf1 53 (by norm_num)
    rw [h53'] at hf1
    norm_num at hf1 ⊢
    exact hf1

  have h221 : f 221 = 445 := by
    have h109' : f 109 = 221 := h109
    specialize hf1 109 (by norm_num)
    rw [h109'] at hf1
    norm_num at hf1 ⊢
    exact hf1

  have h445 : f 445 = 893 := by
    have h221' : f 221 = 445 := h221
    specialize hf1 221 (by norm_num)
    rw [h221'] at hf1
    norm_num at hf1 ⊢
    exact hf1

  have h893 : f 893 = 1789 := by
    have h445' : f 445 = 893 := h445
    specialize hf1 445 (by norm_num)
    rw [h445'] at hf1
    norm_num at hf1 ⊢
    exact hf1

  have h1789 : f 1789 = 3581 := by
    have h893' : f 893 = 1789 := h893
    specialize hf1 893 (by norm_num)
    rw [h893'] at hf1
    norm_num at hf1 ⊢
    exact hf1

  exact h1789