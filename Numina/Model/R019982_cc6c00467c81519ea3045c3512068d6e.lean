import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_150559
  (f : ℝ → ℝ)
  (h₀ : Continuous f)
  (h₁ : ∀ α > 0, Tendsto (λ n => f (n * α)) atTop (𝓝 0))
  : Tendsto f atTop (𝓝 0) := by 
  have h2 := h₁ 1 (by norm_num)
  simpa using h2
  all_goals try { tauto }
  all_goals try { aesop }
  all_goals try { 
    apply tendsto_atTop_ofCauchy
    all_goals try { tauto }
    all_goals try { aesop }
    all_goals try { 
      obtain ⟨α, hα⟩ := h₁ 
      try { tauto } 
    }
  }
  all_goals try { 
    obtain ⟨α, hα⟩ := h₁ 
    try { tauto } 
  }
  all_goals try { 
    apply h₀
    try { tauto }
    all_goals try { 
      obtain ⟨α, hα⟩ := h₁ 
      try { tauto } 
    }
  }
  all_goals try { 
    exact h₀
    all_goals try { 
      obtain ⟨α, hα⟩ := h₁ 
      try { tauto } 
    }
  }
  all_goals try { 
    obtain ⟨α, hα⟩ := h₁ 
    try { tauto } 
  }
  all_goals try { 
    apply h₀
    all_goals try { 
      obtain ⟨α, hα⟩ := h₁ 
      try { tauto } 
    }
  }
  all_goals try { 
    obtain ⟨α, hα⟩ := h₁ 
    try { tauto } 
  }
  all_goals try { tauto }
  all_goals try { 
    apply h₀
    all_goals try { tauto } 
  }
  all_goals try { tauto }
  <;> try { aesop }
  <;> try { 
    apply h₀ 
    all_goals try { tauto } 
    <;> try { aesop }
  }
  <;> try { 
    apply h₀ 
    all_goals try { tauto } 
    <;> try { aesop }
  }
  <;> try { tauto }
  <;> try { tauto }
  <;> try { tauto }
  <;> try { tauto }
  <;> try { tauto }
  <;> try { 
    apply h2 
    all_goals try { tauto } 
  }
  <;> try { 
    apply h₀ 
    all_goals try { tauto } 
  }
  <;> try { 
    obtain ⟨α, hα⟩ := h₁ 
    try { tauto } 
  }
  <;> try { tauto }
  all_goals try { 
    simpa using h2
    all_goals try { tauto }
  }