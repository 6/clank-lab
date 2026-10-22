import Mathlib

/-! The raw matrices, without any assumptions on their parameters. -/
namespace P16c
variable {K : Type*} [Field K]
abbrev Mat (K : Type*) := Matrix (Fin 4) (Fin 4) K

def r (a : K) : Mat K := !![1,1,0,0; 0,1,0,0; a,0,1,1; 0,a,0,1]
def r₁ : Mat K := !![1,0,0,0; 0,1,1,0; 0,0,1,0; 0,0,0,1]
def r₃ (a : K) : Mat K := !![0,0,0,a⁻¹; 0,1,0,0; 0,0,1,0; a,0,0,0]
def T (a b : K) : Mat K := r a * r₁ * r b * r₁
def V (a b : K) : Mat K := r₁ * r b * r₃ a * r b
def T₂ (a b : K) : Mat K := r₁ * T a b * r₁
def V₂ (a b : K) : Mat K := r b * V a b * r b

def traceParam (l : K) : K := l + l⁻¹
def aParam (l m : K) : K := traceParam l ^ 2 / traceParam m
def bParam (l m : K) : K := traceParam l + aParam l m
end P16c
