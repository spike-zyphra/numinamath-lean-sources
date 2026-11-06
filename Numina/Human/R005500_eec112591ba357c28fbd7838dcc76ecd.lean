import Mathlib

open Finset Real Nat
/-How many positive integers n≤2009 have the property that [log_2(n)] is odd?-/

theorem number_theory_608527: {n: ℕ | n ∈ Icc 1 2009 ∧  Odd (log 2 n)}.encard = 682 := by

-- split the range into two parts, 1 to 1023 and 1024 to 2009
  have h_union: {n: ℕ | n ∈ Icc 1 2009 ∧  Odd (log 2 n)} =
  {n: ℕ | n ∈ Icc 1 1023 ∧  Odd (log 2 n)} ∪ {n: ℕ | n ∈ Icc 1024 2009 ∧  Odd (log 2 n)} := by
    ext n
    constructor
    . intro h
      simp only [Set.mem_setOf_eq] at h
      simp at h
      simp [h]
      omega
    . intro h
      simp only [Set.mem_setOf_eq] at h
      simp at h
      simp [h]
      constructor
      . omega
      . rcases h with h | h
        . simp only [h]
        . simp only [h]

  have h_disjoint: Disjoint {n: ℕ | n ∈ Icc 1 1023 ∧  Odd (log 2 n)}  {n: ℕ | n ∈ Icc 1024 2009 ∧  Odd (log 2 n)} := by
    rw [Set.disjoint_iff_forall_ne]
    intro n hn
    intro m hm
    simp only [Set.mem_setOf_eq] at hn hm
    rcases hn with ⟨hn1,hn2⟩
    rcases hm with ⟨hm1,hm2⟩
    simp at hn1 hm1
    omega

  have h_eq: {n: ℕ | n ∈ Icc 1 2009 ∧  Odd (log 2 n)}.encard
  = {n: ℕ | n ∈ Icc 1 1023 ∧  Odd (log 2 n)}.encard + {n: ℕ | n ∈ Icc 1024 2009 ∧  Odd (log 2 n)}.encard := by
    rw [h_union]
    rw [Set.encard_union_eq]
    exact h_disjoint

  have h_count: {n: ℕ | n ∈ Icc 1024 2009 ∧  Odd (log 2 n)}.encard = 0 := by
    have h: ∀ n ∈ Icc 1024 2009, Even (log 2 n) := by
      intro n hn
      simp at hn
      have h1: log 2 n = 10 := by
        rw [Nat.log_eq_iff]
        simp only [hn]
        rcases hn with ⟨h1,h2⟩
        constructor
        . tauto
        . norm_num
          linarith
        norm_num
      rw [h1]
      decide
    rw [Set.encard_eq_zero]
    ext n
    constructor
    . intro hn
      simp only [Set.mem_setOf_eq] at hn
      specialize h n
      simp only [hn] at h
      simp at h
      rcases hn with ⟨hn1,hn2⟩
      absurd hn2
      simp
      exact h
    . tauto
  simp only [h_eq,h_count]
  clear * -

-- repeat the process for the first part, 1 to 1023
  have h_union: {n: ℕ | n ∈ Icc 1 1023 ∧  Odd (log 2 n)} =
  {n: ℕ | n ∈ Icc 1 511 ∧  Odd (log 2 n)} ∪ {n: ℕ | n ∈ Icc 512 1023 ∧  Odd (log 2 n)} := by
    ext n
    constructor
    . intro h
      simp only [Set.mem_setOf_eq] at h
      simp at h
      simp [h]
      omega
    . intro h
      simp only [Set.mem_setOf_eq] at h
      simp at h
      simp [h]
      constructor
      . omega
      . rcases h with h | h
        . simp only [h]
        . simp only [h]

  have h_disjoint: Disjoint {n: ℕ | n ∈ Icc 1 511 ∧  Odd (log 2 n)}  {n: ℕ | n ∈ Icc 512 1023 ∧  Odd (log 2 n)} := by
    rw [Set.disjoint_iff_forall_ne]
    intro n hn
    intro m hm
    simp only [Set.mem_setOf_eq] at hn hm
    rcases hn with ⟨hn1,hn2⟩
    rcases hm with ⟨hm1,hm2⟩
    simp at hn1 hm1
    omega

  have h_eq: {n: ℕ | n ∈ Icc 1 1023 ∧  Odd (log 2 n)}.encard
  = {n: ℕ | n ∈ Icc 1 511 ∧  Odd (log 2 n)}.encard + {n: ℕ | n ∈ Icc 512 1023 ∧  Odd (log 2 n)}.encard := by
    rw [h_union]
    rw [Set.encard_union_eq]
    exact h_disjoint

  have h_count: {n: ℕ | n ∈ Icc 512 1023 ∧  Odd (log 2 n)}.encard = 512 := by
    have set_eq: {n: ℕ | n ∈ Icc 512 1023 ∧  Odd (log 2 n)} = Icc 512 1023 := by
      ext n
      constructor
      . intro hn
        simp only [Set.mem_setOf_eq] at hn
        rcases hn with ⟨hn1,hn2⟩
        norm_cast
      . intro hn
        simp only [Set.mem_setOf_eq] at hn
        simp only [Set.mem_setOf_eq]
        constructor
        . norm_cast
        . simp at hn
          have h1: log 2 n = 9 := by
            rw [Nat.log_eq_iff]
            simp only [hn]
            rcases hn with ⟨h1,h2⟩
            constructor
            . tauto
            . norm_num
              linarith
            norm_num
          rw [h1]
          decide
    rw [set_eq]
    simp [Set.encard]

  simp only [h_eq,h_count]
  clear * -

-- repeat the process for the first part, 1 to 511
  have h_union: {n: ℕ | n ∈ Icc 1 511 ∧  Odd (log 2 n)} =
  {n: ℕ | n ∈ Icc 1 255 ∧  Odd (log 2 n)} ∪ {n: ℕ | n ∈ Icc 256 511 ∧  Odd (log 2 n)} := by
    ext n
    constructor
    . intro h
      simp only [Set.mem_setOf_eq] at h
      simp at h
      simp [h]
      omega
    . intro h
      simp only [Set.mem_setOf_eq] at h
      simp at h
      simp [h]
      constructor
      . omega
      . rcases h with h | h
        . simp only [h]
        . simp only [h]

  have h_disjoint: Disjoint {n: ℕ | n ∈ Icc 1 255 ∧  Odd (log 2 n)}  {n: ℕ | n ∈ Icc 256 511 ∧  Odd (log 2 n)} := by
    rw [Set.disjoint_iff_forall_ne]
    intro n hn
    intro m hm
    simp only [Set.mem_setOf_eq] at hn hm
    rcases hn with ⟨hn1,hn2⟩
    rcases hm with ⟨hm1,hm2⟩
    simp at hn1 hm1
    omega

  have h_eq: {n: ℕ | n ∈ Icc 1 511 ∧  Odd (log 2 n)}.encard
  = {n: ℕ | n ∈ Icc 1 255 ∧  Odd (log 2 n)}.encard + {n: ℕ | n ∈ Icc 256 511 ∧  Odd (log 2 n)}.encard := by
    rw [h_union]
    rw [Set.encard_union_eq]
    exact h_disjoint

  have h_count: {n: ℕ | n ∈ Icc 256 511 ∧  Odd (log 2 n)}.encard = 0 := by
    have h: ∀ n ∈ Icc 256 511, Even (log 2 n) := by
      intro n hn
      simp at hn
      have h1: log 2 n = 8 := by
        rw [Nat.log_eq_iff]
        simp only [hn]
        rcases hn with ⟨h1,h2⟩
        constructor
        . tauto
        . norm_num
          linarith
        norm_num
      rw [h1]
      decide
    rw [Set.encard_eq_zero]
    ext n
    constructor
    . intro hn
      simp only [Set.mem_setOf_eq] at hn
      specialize h n
      simp only [hn] at h
      simp at h
      rcases hn with ⟨hn1,hn2⟩
      absurd hn2
      simp
      exact h
    . tauto

  simp only [h_eq,h_count]
  clear * -

-- repeat the process for the first part, 1 to 255
  have h_union: {n: ℕ | n ∈ Icc 1 255 ∧  Odd (log 2 n)} =
  {n: ℕ | n ∈ Icc 1 127 ∧  Odd (log 2 n)} ∪ {n: ℕ | n ∈ Icc 128 255 ∧  Odd (log 2 n)} := by
    ext n
    constructor
    . intro h
      simp only [Set.mem_setOf_eq] at h
      simp at h
      simp [h]
      omega
    . intro h
      simp only [Set.mem_setOf_eq] at h
      simp at h
      simp [h]
      constructor
      . omega
      . rcases h with h | h
        . simp only [h]
        . simp only [h]

  have h_disjoint: Disjoint {n: ℕ | n ∈ Icc 1 127 ∧  Odd (log 2 n)}  {n: ℕ | n ∈ Icc 128 255 ∧  Odd (log 2 n)} := by
    rw [Set.disjoint_iff_forall_ne]
    intro n hn
    intro m hm
    simp only [Set.mem_setOf_eq] at hn hm
    rcases hn with ⟨hn1,hn2⟩
    rcases hm with ⟨hm1,hm2⟩
    simp at hn1 hm1
    omega

  have h_eq: {n: ℕ | n ∈ Icc 1 255 ∧  Odd (log 2 n)}.encard
  = {n: ℕ | n ∈ Icc 1 127 ∧  Odd (log 2 n)}.encard + {n: ℕ | n ∈ Icc 128 255 ∧  Odd (log 2 n)}.encard := by
    rw [h_union]
    rw [Set.encard_union_eq]
    exact h_disjoint

  have h_count: {n: ℕ | n ∈ Icc 128 255 ∧  Odd (log 2 n)}.encard = 128 := by
    have set_eq: {n: ℕ | n ∈ Icc 128 255 ∧  Odd (log 2 n)} = Icc 128 255 := by
      ext n
      constructor
      . intro hn
        simp only [Set.mem_setOf_eq] at hn
        rcases hn with ⟨hn1,hn2⟩
        norm_cast
      . intro hn
        simp only [Set.mem_setOf_eq] at hn
        simp only [Set.mem_setOf_eq]
        constructor
        . norm_cast
        . simp at hn
          have h1: log 2 n = 7 := by
            rw [Nat.log_eq_iff]
            simp only [hn]
            rcases hn with ⟨h1,h2⟩
            constructor
            . tauto
            . norm_num
              linarith
            norm_num
          rw [h1]
          decide
    rw [set_eq]
    simp [Set.encard]

  simp only [h_eq,h_count]
  clear * -

  -- repeat the process for the first part, 1 to 127
  have h_union: {n: ℕ | n ∈ Icc 1 127 ∧  Odd (log 2 n)} =
  {n: ℕ | n ∈ Icc 1 63 ∧  Odd (log 2 n)} ∪ {n: ℕ | n ∈ Icc 64 127 ∧  Odd (log 2 n)} := by
    ext n
    constructor
    . intro h
      simp only [Set.mem_setOf_eq] at h
      simp at h
      simp [h]
      omega
    . intro h
      simp only [Set.mem_setOf_eq] at h
      simp at h
      simp [h]
      constructor
      . omega
      . rcases h with h | h
        . simp only [h]
        . simp only [h]

  have h_disjoint: Disjoint {n: ℕ | n ∈ Icc 1 63 ∧  Odd (log 2 n)}  {n: ℕ | n ∈ Icc 64 127 ∧  Odd (log 2 n)} := by
    rw [Set.disjoint_iff_forall_ne]
    intro n hn
    intro m hm
    simp only [Set.mem_setOf_eq] at hn hm
    rcases hn with ⟨hn1,hn2⟩
    rcases hm with ⟨hm1,hm2⟩
    simp at hn1 hm1
    omega

  have h_eq: {n: ℕ | n ∈ Icc 1 127 ∧  Odd (log 2 n)}.encard
  = {n: ℕ | n ∈ Icc 1 63 ∧  Odd (log 2 n)}.encard + {n: ℕ | n ∈ Icc 64 127 ∧  Odd (log 2 n)}.encard := by
    rw [h_union]
    rw [Set.encard_union_eq]
    exact h_disjoint

  have h_count: {n: ℕ | n ∈ Icc 64 127 ∧  Odd (log 2 n)}.encard = 0 := by
    have h: ∀ n ∈ Icc 64 127, Even (log 2 n) := by
      intro n hn
      simp at hn
      have h1: log 2 n = 6 := by
        rw [Nat.log_eq_iff]
        simp only [hn]
        rcases hn with ⟨h1,h2⟩
        constructor
        . tauto
        . norm_num
          linarith
        norm_num
      rw [h1]
      decide
    rw [Set.encard_eq_zero]
    ext n
    constructor
    . intro hn
      simp only [Set.mem_setOf_eq] at hn
      specialize h n
      simp only [hn] at h
      simp at h
      rcases hn with ⟨hn1,hn2⟩
      absurd hn2
      simp
      exact h
    . tauto

  simp only [h_eq,h_count]
  clear * -

  -- repeat the process for the first part, 1 to 63
  have h_union: {n: ℕ | n ∈ Icc 1 63 ∧  Odd (log 2 n)} =
  {n: ℕ | n ∈ Icc 1 31 ∧  Odd (log 2 n)} ∪ {n: ℕ | n ∈ Icc 32 63 ∧  Odd (log 2 n)} := by
    ext n
    constructor
    . intro h
      simp only [Set.mem_setOf_eq] at h
      simp at h
      simp [h]
      omega
    . intro h
      simp only [Set.mem_setOf_eq] at h
      simp at h
      simp [h]
      constructor
      . omega
      . rcases h with h | h
        . simp only [h]
        . simp only [h]

  have h_disjoint: Disjoint {n: ℕ | n ∈ Icc 1 31 ∧  Odd (log 2 n)}  {n: ℕ | n ∈ Icc 32 63 ∧  Odd (log 2 n)} := by
    rw [Set.disjoint_iff_forall_ne]
    intro n hn
    intro m hm
    simp only [Set.mem_setOf_eq] at hn hm
    rcases hn with ⟨hn1,hn2⟩
    rcases hm with ⟨hm1,hm2⟩
    simp at hn1 hm1
    omega

  have h_eq: {n: ℕ | n ∈ Icc 1 63 ∧  Odd (log 2 n)}.encard
  = {n: ℕ | n ∈ Icc 1 31 ∧  Odd (log 2 n)}.encard + {n: ℕ | n ∈ Icc 32 63 ∧  Odd (log 2 n)}.encard := by
    rw [h_union]
    rw [Set.encard_union_eq]
    exact h_disjoint

  have h_count: {n: ℕ | n ∈ Icc 32 63 ∧  Odd (log 2 n)}.encard = 32 := by
    have set_eq: {n: ℕ | n ∈ Icc 32 63 ∧  Odd (log 2 n)} = Icc 32 63 := by
      ext n
      constructor
      . intro hn
        simp only [Set.mem_setOf_eq] at hn
        rcases hn with ⟨hn1,hn2⟩
        norm_cast
      . intro hn
        simp only [Set.mem_setOf_eq] at hn
        simp only [Set.mem_setOf_eq]
        constructor
        . norm_cast
        . simp at hn
          have h1: log 2 n = 5 := by
            rw [Nat.log_eq_iff]
            simp only [hn]
            rcases hn with ⟨h1,h2⟩
            constructor
            . tauto
            . norm_num
              linarith
            norm_num
          rw [h1]
          decide
    rw [set_eq]

    simp [Set.encard]
  simp only [h_eq,h_count]
  clear * -

  -- repeat the process for the first part, 1 to 31
  have h_union: {n: ℕ | n ∈ Icc 1 31 ∧  Odd (log 2 n)} =
  {n: ℕ | n ∈ Icc 1 15 ∧  Odd (log 2 n)} ∪ {n: ℕ | n ∈ Icc 16 31 ∧  Odd (log 2 n)} := by
    ext n
    constructor
    . intro h
      simp only [Set.mem_setOf_eq] at h
      simp at h
      simp [h]
      omega
    . intro h
      simp only [Set.mem_setOf_eq] at h
      simp at h
      simp [h]
      constructor
      . omega
      . rcases h with h | h
        . simp only [h]
        . simp only [h]

  have h_disjoint: Disjoint {n: ℕ | n ∈ Icc 1 15 ∧  Odd (log 2 n)}  {n: ℕ | n ∈ Icc 16 31 ∧  Odd (log 2 n)} := by
    rw [Set.disjoint_iff_forall_ne]
    intro n hn
    intro m hm
    simp only [Set.mem_setOf_eq] at hn hm
    rcases hn with ⟨hn1,hn2⟩
    rcases hm with ⟨hm1,hm2⟩
    simp at hn1 hm1
    omega

  have h_eq: {n: ℕ | n ∈ Icc 1 31 ∧  Odd (log 2 n)}.encard
  = {n: ℕ | n ∈ Icc 1 15 ∧  Odd (log 2 n)}.encard + {n: ℕ | n ∈ Icc 16 31 ∧  Odd (log 2 n)}.encard := by
    rw [h_union]
    rw [Set.encard_union_eq]
    exact h_disjoint

  have h_count: {n: ℕ | n ∈ Icc 16 31 ∧  Odd (log 2 n)}.encard = 0 := by
    have h: ∀ n ∈ Icc 16 31, Even (log 2 n) := by
      intro n hn
      simp at hn
      have h1: log 2 n = 4 := by
        rw [Nat.log_eq_iff]
        simp only [hn]
        rcases hn with ⟨h1,h2⟩
        constructor
        . tauto
        . norm_num
          linarith
        norm_num
      rw [h1]
      decide
    rw [Set.encard_eq_zero]
    ext n
    constructor
    . intro hn
      simp only [Set.mem_setOf_eq] at hn
      specialize h n
      simp only [hn] at h
      simp at h
      rcases hn with ⟨hn1,hn2⟩
      absurd hn2
      simp
      exact h
    . tauto

  simp only [h_eq,h_count]
  clear * -

  -- repeat the process for the first part, 1 to 15
  have h_union: {n: ℕ | n ∈ Icc 1 15 ∧  Odd (log 2 n)} =
  {n: ℕ | n ∈ Icc 1 7 ∧  Odd (log 2 n)} ∪ {n: ℕ | n ∈ Icc 8 15 ∧  Odd (log 2 n)} := by
    ext n
    constructor
    . intro h
      simp only [Set.mem_setOf_eq] at h
      simp at h
      simp [h]
      omega
    . intro h
      simp only [Set.mem_setOf_eq] at h
      simp at h
      simp [h]
      constructor
      . omega
      . rcases h with h | h
        . simp only [h]
        . simp only [h]

  have h_disjoint: Disjoint {n: ℕ | n ∈ Icc 1 7 ∧  Odd (log 2 n)}  {n: ℕ | n ∈ Icc 8 15 ∧  Odd (log 2 n)} := by
    rw [Set.disjoint_iff_forall_ne]
    intro n hn
    intro m hm
    simp only [Set.mem_setOf_eq] at hn hm
    rcases hn with ⟨hn1,hn2⟩
    rcases hm with ⟨hm1,hm2⟩
    simp at hn1 hm1
    omega

  have h_eq: {n: ℕ | n ∈ Icc 1 15 ∧  Odd (log 2 n)}.encard
  = {n: ℕ | n ∈ Icc 1 7 ∧  Odd (log 2 n)}.encard + {n: ℕ | n ∈ Icc 8 15 ∧  Odd (log 2 n)}.encard := by
    rw [h_union]
    rw [Set.encard_union_eq]
    exact h_disjoint

  have h_count: {n: ℕ | n ∈ Icc 8 15 ∧  Odd (log 2 n)}.encard = 8 := by
    have set_eq: {n: ℕ | n ∈ Icc 8 15 ∧  Odd (log 2 n)} = Icc 8 15 := by
      ext n
      constructor
      . intro hn
        simp only [Set.mem_setOf_eq] at hn
        rcases hn with ⟨hn1,hn2⟩
        norm_cast
      . intro hn
        simp only [Set.mem_setOf_eq] at hn
        simp only [Set.mem_setOf_eq]
        constructor
        . norm_cast
        . simp at hn
          have h1: log 2 n = 3 := by
            rw [Nat.log_eq_iff]
            simp only [hn]
            rcases hn with ⟨h1,h2⟩
            constructor
            . tauto
            . norm_num
              linarith
            norm_num
          rw [h1]
          decide
    rw [set_eq]
    simp [Set.encard]

  simp only [h_eq,h_count]
  clear * -

  -- repeat the process for the first part, 1 to 7
  have h_union: {n: ℕ | n ∈ Icc 1 7 ∧  Odd (log 2 n)} =
  {n: ℕ | n ∈ Icc 1 3 ∧  Odd (log 2 n)} ∪ {n: ℕ | n ∈ Icc 4 7 ∧  Odd (log 2 n)} := by
    ext n
    constructor
    . intro h
      simp only [Set.mem_setOf_eq] at h
      simp at h
      simp [h]
      omega
    . intro h
      simp only [Set.mem_setOf_eq] at h
      simp at h
      simp [h]
      constructor
      . omega
      . rcases h with h | h
        . rcases h with ⟨h1,h2⟩
          simp only [h2]
        . simp only [h]

  have h_disjoint: Disjoint {n: ℕ | n ∈ Icc 1 3 ∧  Odd (log 2 n)}  {n: ℕ | n ∈ Icc 4 7 ∧  Odd (log 2 n)} := by
    rw [Set.disjoint_iff_forall_ne]
    intro n hn
    intro m hm
    simp only [Set.mem_setOf_eq] at hn hm
    rcases hn with ⟨hn1,hn2⟩
    rcases hm with ⟨hm1,hm2⟩
    simp at hn1 hm1
    omega

  have h_eq: {n: ℕ | n ∈ Icc 1 7 ∧  Odd (log 2 n)}.encard
  = {n: ℕ | n ∈ Icc 1 3 ∧  Odd (log 2 n)}.encard + {n: ℕ | n ∈ Icc 4 7 ∧  Odd (log 2 n)}.encard := by
    rw [h_union]
    rw [Set.encard_union_eq]
    exact h_disjoint

  have h_count: {n: ℕ | n ∈ Icc 4 7 ∧  Odd (log 2 n)}.encard = 0 := by
    have h: ∀ n ∈ Icc 4 7, Even (log 2 n) := by
      intro n hn
      simp at hn
      have h1: log 2 n = 2 := by
        rw [Nat.log_eq_iff]
        simp only [hn]
        rcases hn with ⟨h1,h2⟩
        constructor
        . tauto
        . norm_num
          linarith
        norm_num
      rw [h1]
      decide
    rw [Set.encard_eq_zero]
    ext n
    constructor
    . intro hn
      simp only [Set.mem_setOf_eq] at hn
      specialize h n
      simp only [hn] at h
      simp at h
      rcases hn with ⟨hn1,hn2⟩
      absurd hn2
      simp
      exact h
    . tauto

  simp only [h_eq,h_count]
  clear * -
  -- repeat the process for the first part, 1 to 3
  have h_union: {n: ℕ | n ∈ Icc 1 3 ∧  Odd (log 2 n)} =
  {n: ℕ | n ∈ Icc 1 1 ∧  Odd (log 2 n)} ∪ {n: ℕ | n ∈ Icc 2 3 ∧  Odd (log 2 n)} := by
    ext n
    constructor
    . intro h
      simp only [Set.mem_setOf_eq] at h
      simp at h
      simp [h]
      omega
    . intro h
      simp only [Set.mem_setOf_eq] at h
      simp at h
      simp [h]
      constructor
      . omega
      . rcases h with h | h
        . rcases h with ⟨h1,h2⟩
          simp only [h2]
        . simp only [h]

  have h_disjoint: Disjoint {n: ℕ | n ∈ Icc 1 1 ∧  Odd (log 2 n)}  {n: ℕ | n ∈ Icc 2 3 ∧  Odd (log 2 n)} := by
    rw [Set.disjoint_iff_forall_ne]
    intro n hn
    intro m hm
    simp only [Set.mem_setOf_eq] at hn hm
    rcases hn with ⟨hn1,hn2⟩
    rcases hm with ⟨hm1,hm2⟩
    simp at hn1 hm1
    omega

  have h_eq: {n: ℕ | n ∈ Icc 1 3 ∧  Odd (log 2 n)}.encard
  = {n: ℕ | n ∈ Icc 1 1 ∧  Odd (log 2 n)}.encard + {n: ℕ | n ∈ Icc 2 3 ∧  Odd (log 2 n)}.encard := by
    rw [h_union]
    rw [Set.encard_union_eq]
    exact h_disjoint

  have h_count: {n: ℕ | n ∈ Icc 2 3 ∧  Odd (log 2 n)}.encard = 2 := by
    have set_eq: {n: ℕ | n ∈ Icc 2 3 ∧  Odd (log 2 n)} = Icc 2 3 := by
      ext n
      constructor
      . intro hn
        simp only [Set.mem_setOf_eq] at hn
        rcases hn with ⟨hn1,hn2⟩
        norm_cast
      . intro hn
        simp only [Set.mem_setOf_eq] at hn
        simp only [Set.mem_setOf_eq]
        constructor
        . norm_cast
        . simp at hn
          have h1: log 2 n = 1 := by
            rw [Nat.log_eq_iff]
            simp only [hn]
            rcases hn with ⟨h1,h2⟩
            constructor
            . tauto
            . norm_num
              linarith
            norm_num
          rw [h1]
          decide
    rw [set_eq]
    simp [Set.encard]

  simp only [h_eq,h_count]
  clear * -

  -- Finally, we can compute the total
  have final_count: {n | n ∈ Icc 1 1 ∧ Odd (Nat.log 2 n)}.encard = 0 := by
    simp
    ext n
    constructor
    . intro hn
      simp only [Set.mem_setOf_eq] at hn
      rcases hn with ⟨hn1,hn2⟩
      simp [hn1] at hn2
    . tauto

  rw [final_count]
  norm_num