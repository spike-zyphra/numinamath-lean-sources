import Mathlib

open BigOperators Finset Nat

/-
Let $N$ be a positive integer. Consider an $N \times N$ chessboard where rows are indexed
by $r \in \{0, 1, \ldots, N-1\}$ from top to bottom, and columns are indexed
by $c \in \{0, 1, \ldots, N-1\}$ from left to right. The number assigned to the square $(r,c)$
is $N \cdot r + c + 1$. A square $(r,c)$ is black if $r+c$ is an even integer.
(Note that square $(0,0)$ contains the number 1 and is black, consistent with these definitions).
Determine the number of black squares that contain odd numbers.
Show that this number is $N^2/4$ if $N$ is even, and $(N^2+1)/2$ if $N$ is odd.
-/

-- mainly prove ncard_prod
@[simp]
lemma ENat.toNat_mul (a b : ℕ∞) : (a * b).toNat = a.toNat * b.toNat := by
  cases a <;> cases b <;> simp
  · rename_i b; cases b <;> simp
  · rename_i a; cases a <;> simp
  · rw [← coe_mul, toNat_coe]

@[simp]
lemma ENat.card_prod (α β : Type*) : ENat.card (α × β) = .card α * .card β := by
  simp [ENat.card]

@[simp]
lemma Set.encard_prod {α β : Type*} (s : Set α) (t : Set β) : (s ×ˢ t).encard = s.encard * t.encard := by
  simp [Set.encard, ENat.card_congr (Equiv.Set.prod ..)]

@[simp]
lemma Set.ncard_prod {α β : Type*} (s : Set α) (t : Set β) : (s ×ˢ t).ncard = s.ncard * t.ncard := by
  simp [ncard, ENat.toNat_mul]



-- if N is even, then the number of r or c with Even numbers is N / 2
@[simp]
lemma N_Even_SetCard (N : ℕ) (hN : Even N) : #(image (fun k => k * 2) (range (N / 2))) = N / 2 := by
  have : (range N).card = N := by field_simp
  rw [Finset.card_image_of_injective]
  ·
    have : 2 ∣ N := by exact even_iff_two_dvd.mp hN
    field_simp
  ·
    intro x y h
    linarith

-- if N is Evenm, then the number of black squares with Even r and Even c is N^2 / 4
@[simp]
lemma N_Even_r_Even_c_Even (N : ℕ) (hN : Even N) :
    {(r, c) : ℕ × ℕ | r < N ∧ c < N ∧ Even r ∧ Even c}.ncard = N ^ 2 / 4 := by

  have h_N_dvd_2 : 2 ∣ N := by exact even_iff_two_dvd.mp hN
  -- First establish that even numbers less than N form range (N/2)
  have even_range : {r : ℕ | r < N ∧ Even r} = Set.image (fun k => k * 2) (↑(range (N / 2))) := by
    ext r
    simp
    constructor
    -- split `⊢ r < N ∧ Even r ↔ ∃ x < N / 2, x * 2 = r` into 2 cases
    -- ⊢ r < N ∧ Even r → ∃ x < N / 2, x * 2 = r
    · intro ⟨hr, hr_even⟩
      obtain ⟨k, hk⟩ := hr_even
      use k
      constructor
      replace hk : r = 2 * k := by linarith
      · rw [hk] at hr
        omega
      ·
        linarith
    -- ⊢ (∃ x < N / 2, x * 2 = r) → r < N ∧ Even r
    · intro ⟨k, hk_bound, hk_eq⟩
      constructor
      · rw [← hk_eq]
        omega
      · use k; omega

  -- The set equals the product of even ranges
  have : {(r, c) : ℕ × ℕ | r < N ∧ c < N ∧ Even r ∧ Even c} =
         Set.image (fun k => (k * 2)) (↑(range (N / 2))) ×ˢ
         Set.image (fun k => (k * 2)) (↑(range (N / 2))) := by
    ext ⟨r, c⟩
    simp
    constructor
    /- split `⊢ r < N ∧ c < N ∧ Even r ∧ Even c ↔
    -- (r, c) ∈ Set.image (fun k => k * 2) (↑(range (N / 2))) ×ˢ
    Set.image (fun k => k * 2) (↑(range (N / 2)))` -/

    · intro ⟨hr, hc, hr_even, hc_even⟩
      obtain ⟨kr, hkr⟩ := hr_even
      obtain ⟨kc, hkc⟩ := hc_even

      constructor
      ·
      -- use kr, kc
        use kr
        rw [hkr] at hr
        constructor
        . omega
        . omega
      ·
        use kc
        rw [hkc] at hc
        constructor
        . omega
        . omega
    -- ⊢ ((∃ x < N / 2, x * 2 = r) ∧ ∃ x < N / 2, x * 2 = c) → r < N ∧ c < N ∧ Even r ∧ Even c
    · intro h
      constructor
      · omega
      · constructor
        . omega
        . constructor
          . bound
          . bound

  rw [this]
  -- Use cardinality of product and the fact that N is even
  have hN_div : N = 2 * (N / 2) := by exact Eq.symm (two_mul_div_two_of_even hN)
  norm_cast

  simp [N_Even_SetCard N hN]
  rw [← pow_two]

  -- the goal now is : ⊢ (N / 2) ^ 2 = N ^ 2 / 4
  have : N ^ 2 / 4 = (N / 2) ^ 2 := by
    have : N = (N / 2) * 2 := by exact Eq.symm (div_two_mul_two_of_even hN)
    calc
      _ = ((N / 2) * 2) ^ 2 / 4 := by nth_rw 1 [this]
      _ = (N / 2) ^ 2 * 2 ^ 2 / 4 := by group
      _ = (N / 2) ^ 2 := by norm_num
  linarith


-- Finset range (k + 1) has k + 1 elements
@[simp]
lemma set_rangeN_card (k : ℕ) :  #(image (fun j => j * 2) (range (k + 1))) = k + 1 := by
  have : (range (k + 1)).card = k + 1 := by field_simp
  rw [Finset.card_image_of_injective]
  .
    field_simp
  .
    intro x y h
    linarith

-- if N is Odd, and r c with Even numbers, the black squares are (N + 1) ^ 2 / 4
@[simp]
lemma N_Odd_r_Even_c_Even (N : ℕ) (hN : Odd N) :
    {(r, c) : ℕ × ℕ | r < N ∧ c < N ∧ Even r ∧ Even c}.ncard = (N + 1) ^ 2 / 4 := by

  -- First, express N in terms of 2k + 1
  obtain ⟨k, hk⟩ := hN

  -- Show that even numbers < N are exactly {0, 2, 4, ..., 2k}
  have h_even_count : {r : ℕ | r < N ∧ Even r}.ncard = k + 1 := by
    rw [hk]
    -- The even numbers less than 2k + 1 are 0, 2, 4, ..., 2k
    -- This can be proven by showing bijection with range(k + 1)
    have h_even_range : {r : ℕ | r < N ∧ Even r} = Set.image (fun j => j * 2) (range (k + 1)) := by
      ext r
      simp
      constructor
      . intro ⟨hr, hr_even⟩
        obtain ⟨j, hj⟩ := hr_even
        use j
        constructor
        . omega
        . omega
      . intro ⟨j, hj_bound, hj_eq⟩
        constructor
        . rw [← hj_eq]
          omega
        . use j; omega
    rw [hk] at h_even_range ; rw [h_even_range]
    norm_cast
    simp

  -- Use the fact that the set is a Cartesian product
  -- Split the condition into separate sets for r and c
  have h_prod : {(r, c) : ℕ × ℕ | r < N ∧ c < N ∧ Even r ∧ Even c} =
    {r : ℕ | r < N ∧ Even r} ×ˢ {c : ℕ | c < N ∧ Even c} := by
    ext ⟨r, c⟩
    simp [Set.mem_prod]
    constructor
    .
      intro ⟨hr, hc, hr_even, hc_even⟩
      obtain ⟨kr, hkr⟩ := hr_even
      obtain ⟨kc, hkc⟩ := hc_even
      .
        constructor
        . constructor
          . omega
          . bound
        . constructor
          . omega
          . bound
    .
      intro h
      bound
  rw [h_prod]
  simp
  rw [h_even_count, hk]
  ring_nf
  omega




@[simp]
lemma N_Odd_SetCard (N : ℕ) (hN : Odd N) :
    #(image (fun k => 2 * k + 1) (range ((N - 1) / 2))) = (N - 1) / 2 := by
  obtain ⟨k, hk⟩ := hN
  have h_N_sub_1_dvd_2 : 2 ∣ (N - 1) := by bound
  have : (range N).card = N := by field_simp
  rw [Finset.card_image_of_injective]
  ·
    -- norm_cast
    field_simp

  · intro x y h
    linarith

-- if N is Odd, and r c with Odd numbers, the black squares are (N - 1) ^ 2 / 4
@[simp]
lemma N_Odd_r_Odd_c_Odd (N : ℕ) (hN : Odd N) :
    {(r, c) : ℕ × ℕ | r < N ∧ c < N ∧ Odd r ∧ Odd c}.ncard = (N - 1) ^ 2 / 4 := by

  obtain ⟨k, hk⟩ := hN
  have h_N_sub_1_dvd_2 : 2 ∣ (N - 1) := by bound
  -- Convert to Finset for easier counting
  have equiv : {(r, c) : ℕ × ℕ | r < N ∧ c < N ∧ Odd r ∧ Odd c} =
               ((Finset.range N).filter Odd ×ˢ (Finset.range N).filter Odd : Set (ℕ × ℕ)) := by
    ext ⟨r, c⟩
    simp [Finset.mem_product, Finset.mem_filter, Finset.mem_range]
    bound

  rw [equiv]
  -- rw [Set.ncard_prod]
  simp [Set.ncard_coe_Finset]

  -- First convert the set notation to Finset.filter
  have set_eq_filter : {x | x < N ∧ Odd x} = (Finset.range N).filter Odd := by
    ext x
    simp [Finset.mem_filter, Finset.mem_range]

  rw [set_eq_filter]

  -- Now prove that |{odd numbers < N}| = (N-1)/2 when N is odd
  have odd_count : (Finset.range N).filter Odd =
      Finset.image (fun k => 2 * k + 1) (Finset.range ((N - 1) / 2)) := by

    ext r
    simp [Finset.mem_filter, Finset.mem_range]
    constructor
    .
      intro ⟨hr, hr_odd⟩
      obtain ⟨k, hk⟩ := hr_odd
      use k
      constructor
      . omega
      . omega
    .
      intro ⟨k, hk_bound, hk_eq⟩
      constructor
      .
        omega
      . bound
    -- This establishes the bijection between odd numbers < N and {0,1,...,(N-1)/2}

  rw [odd_count]
  norm_cast
  have hN : Odd N := by bound
  simp [N_Odd_SetCard N hN]
  rw [hk] ; simp
  have : (2 * k) ^ 2 = k * k * 4 := by group
  rw [this]
  field_simp

-- if a + b is odd, then one of them is even and the other is odd
@[simp]
lemma lemma_sum_Odd_One_Odd (a b : ℕ) (h : Odd (a + b)) (ha : Odd a) : Even b := by
  by_contra hb
  replace hb : Odd b := by exact not_even_iff_odd.mp hb
  have h' : Even (a + b) := by exact Odd.add_odd ha hb
  exact not_even_iff_odd.mpr h h'

-- if a + b is even, and one is Even, then the other is even
@[simp]
lemma lemma_sum_Even_one_Even (a b : ℕ) (h : Even (b + a)) (ha : Even a) : Even b := by
  obtain ⟨k, hk⟩ := ha
  obtain ⟨m, hm⟩ := h
  rw [hk] at hm
  use m - k
  omega

-- if N is Odd, calculate (N + 1) ^ 2 / 4 + (N - 1) ^ 2 / 4
@[simp]
lemma lemma_N_Odd_black_Odd (N: ℕ) (hN : Odd N) :
    (N + 1) ^ 2 / 4 + (N - 1) ^ 2 / 4 = (N ^ 2 + 1) / 2:= by
  obtain ⟨k, hk⟩ := hN
  have hN : Odd N := by rw [hk]; use k
  rw [hk]
  -- ring_nf
  have h1 : (2 * k + 1 + 1) ^ 2 = 4 * (k + 1) ^ 2 := by group
  have h2 : (2 * k + 1 - 1) ^ 2 = 4 * k ^ 2 := by field_simp ; group

  have h3 : (2 * k + 1) ^ 2 + 1 = (2 * k ^ 2 + 2 * k + 1) * 2 := by group
  rw [h1, h2, h3] ; clear h1 h2 h3
  simp ; group


-- marin throrem
theorem number_theory_636855 (N : ℕ) (Set_N : Set (ℕ × ℕ))
    (Set_N_Odd1 : Set (ℕ × ℕ)) (Set_N_Odd2 : Set (ℕ × ℕ))
    (h_Set_N_Odd1 : Set_N_Odd1 = {(r, c) : ℕ × ℕ | r < N ∧ c < N ∧ Even r ∧ Even c})
    (h_Set_N_Odd2 : Set_N_Odd2 = {(r, c) : ℕ × ℕ | r < N ∧ c < N ∧ Odd r ∧ Odd c})
    (h_Set_N : Set_N = {(r, c) : ℕ × ℕ | r < N ∧ c < N ∧ Even (r + c) ∧ Odd (N * r + c + 1)}) :
    if Even N then Set_N.ncard = N ^ 2 / 4
    else Set_N_Odd1.ncard + Set_N_Odd2.ncard = (N ^ 2 + 1) / 2 := by

  rw [h_Set_N]
  -- split ifs into 2 cases
  split_ifs with hN
  .
    -- N is even
    have : {(r, c) : ℕ × ℕ | r < N ∧ c < N ∧ Even (r + c) ∧ Odd (N * r + c + 1)} =
        {(r, c) : ℕ × ℕ | r < N ∧ c < N ∧ Even r ∧ Even c} := by
      ext ⟨r, c⟩
      simp
      intro hrN hcN
      constructor
      .
        -- prove the goal `⊢ Even (r + c) ∧ Odd (N * r + c + 1) → Even r ∧ Even c`
        intro h
        obtain ⟨hr_even, h_odd⟩ := h
        rw [show N * r + c + 1 = (N * r + 1) + c by ring] at h_odd
        have : Odd (N * r + 1) := by field_simp
        have h_Even_c: Even c := by field_simp
        have h_Even_r : Even r := by field_simp
        -- constructor
        exact ⟨h_Even_r, h_Even_c⟩
      .
        -- prove the goal `⊢ Even r ∧ Even c → Even (r + c) ∧ Odd (N * r + c + 1)`,
        -- although it is not needed
        intro h
        obtain ⟨hr_even, hc_even⟩ := h
        have h_even_r_add_c : Even (r + c) := by exact Even.add hr_even hc_even
        have h_odd_N_r_c_1 : Odd (N * r + 1) := by field_simp
        have : Odd (N * r + c + 1) := by
          rw [show N * r + c + 1 = (N * r + 1) + c by ring]
          exact Even.odd_add hc_even h_odd_N_r_c_1
        exact ⟨h_even_r_add_c, this⟩
    rw [this]
    field_simp
  .
    -- N is Odd
    replace hN : Odd N := by exact not_even_iff_odd.mp hN
    rw [h_Set_N_Odd1] ; field_simp
    rw [h_Set_N_Odd2] ; field_simp
    -- goal solved
