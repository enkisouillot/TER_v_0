/-
Ce fichier a pour but de débuter l'étude du cours d'analyse complexe de Master via LEAN.
Nous allons y étudier les premières propriétés des fonctions holomorphes.
Nous passerons le sujet des fonctions analytiques car celles-ci ont été développées dans d'autres fichiers, auquels nous pourrons faire référence. 

-/

-- Importons les datas qui nous seront utiles. 

import data.complex.basic -- pour travailler sur ℂ
import analysis.complex.basic -- pour travailler sur ℂ
import analysis.calculus.deriv -- pour utiliser la dérivation déjà créée de façon générale
import topology.basic


open complex
/-
Afin de gagner en concision pour ce projet, nous allons créer le caractère "être holomorphe" pour une fonction
-/

def is_C_deriv_at (Ω : set ℂ)(f : ℂ → ℂ)(z₀ : ℂ)(ho : is_open Ω)(hz : z₀ ∈ Ω) : Prop :=
∃ (f' : ℂ), has_deriv_within_at f f' Ω z₀

-- has_deriv_at 

def is_C_deriv (Ω : set ℂ)(f : ℂ → ℂ)(ho : is_open Ω) : Prop := 
∃ (f' : ℂ → ℂ), ∀ z ∈ Ω, has_deriv_at f (f' z) z

-- equiv_real_prod (to_fun : ℂ → ℝ²) (inv_fun : ℝ² → ℂ)

def realify (f : ℂ → ℂ ) : (ℝ × ℝ → ℝ × ℝ) := equiv_real_prod.to_fun ∘ f ∘ equiv_real_prod.inv_fun

def multiplication (z : ℂ) : (ℝ × ℝ →L[ℝ] ℝ × ℝ) := by {
  refine ⟨_,_⟩,
  { refine ⟨_,_,_⟩,
    { exact realify (λ w, z * w) },
    { intros, simp [realify], split, ring, ring },
    { intros, simp [realify], split; ring } },
  { simp, 
    apply continuous_def.mpr,
    intros s hs,
    refine is_open_iff_open_ball_subset.mpr _,
    sorry
  }
}

variables {Ω : set ℂ} {f : Ω → ℂ} {z₀ : Ω}

-- lemma cauchy_riemann (hf : f is_C_deriv) :=
