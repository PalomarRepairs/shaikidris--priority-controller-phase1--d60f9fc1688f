module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Basic.Assignments

@[expose] public section

namespace Controller

/-- Incidences are charged with multiplicity; roots include repeated outputs. -/
structure DecoderSize where
  channels : ℕ
  nodes : ℕ
  children : ℕ
  guards : ℕ
  roots : ℕ
  deriving Repr, DecidableEq

def DecoderSize.total (s : DecoderSize) : ℕ :=
  s.channels + s.nodes + s.children + s.guards + s.roots

structure NativeSize where
  variableCount : ℕ
  clauses : ℕ
  literals : ℕ
  deriving Repr, DecidableEq

def NativeSize.total (s : NativeSize) : ℕ := s.variableCount + s.clauses + s.literals

structure HornSize where
  variableCount : ℕ
  clauses : ℕ
  literals : ℕ
  deriving Repr, DecidableEq

def HornSize.total (s : HornSize) : ℕ := 1 + s.variableCount + s.clauses + s.literals

structure FactorSize where
  factors : ℕ
  terms : ℕ
  guards : ℕ
  conflicts : ℕ
  deriving Repr, DecidableEq

def FactorSize.total (s : FactorSize) : ℕ := s.factors + s.terms + s.guards + s.conflicts

/-- Each cone cost excludes ambient channel initialization. -/
def coneOverlapSize (n G : ℕ) (coneCosts : List ℕ) : ℕ := n + G + coneCosts.sum

structure OutputSize where
  models : ℕ
  proofRows : ℕ
  proofLiterals : ℕ
  serializedBytes : ℕ
  deriving Repr, DecidableEq

end Controller
