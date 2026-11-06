import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_13701 {f : ℝ → ℝ} (hodd : Odd f) :
    Odd (f ∘ f ∘ f) := by
  obtain ⟨n, hn⟩ := hodd
  use (f ∘ f ∘ f - 1) / 2
  funext x
  simp [Function.comp_apply, hn] at *
  <;> ring_nf <;> norm_num
  all_goals
    try { aesop }
    <;> try { linarith }
    all_goals
      try { nlinarith }
      all_goals
        try { norm_num }
        <;> try { tauto }
        <;> try { linarith }
        <;> try { nlinarith }
        <;> norm_num
        <;> try { try { trivial } } <;> exfalso <;> try { trivial }
        all_goals
          nlinarith
          <;> norm_num
          <;> try { try { trivial } } <;> try { try { tauto } }
          <;> nlinarith
          <;> norm_num
          <;> try { try { trivial } } <;> try { try { tauto } }
          all_goals
            try { 
              have : 1 = 2 := by 
                try { linarith }
                <;> try { tauto }
              contradiction
            }
            all_goals tauto
  all_goals
    try { linarith } <;> try { nlinarith } <;> try { contradiction }
    -- could be norm_num
    <;> try { try { exfalso } <;> linarith }
    all_goals
      try { linarith }
      <;> try { nlinarith }
      all_goals
        try { linarith }
        <;> try { nlinarith }
  all_goals
    try { 
      exfalso
      <;> try { 
        nlinarith
        <;> norm_num
        <;> try { try { contradiction } }
      }
    }
    all_goals
      try { 
        exfalso
        <;> try { exfalso }
        <;> try { 
          have h : 0 = 1 := by
            try { 
              nlinarith 
              <;> try { contradiction }
              <;> try { 
                nlinarith
                <;> try { contradiction }
              } 
            }
          contradiction
        }
      }
  all_goals
    try { 
      have h6 : 0 = 1 := by 
        try { linarith }
        <;> try { try { tauto } }
        <;> try { 
          exfalso
          <;> try { try { contradiction } }
          <;> try { try { tauto } }
        }
        try { tauto }
      contradiction
    }
    <;> try { contradiction }
    <;> try { tauto }
  all_goals tauto
  all_goals norm_num