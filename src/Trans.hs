-- Module Trans: program transformation

module Trans where

import Term
import Exception
import Prelude hiding ((<>))
import Data.Maybe
import Data.List
import Data.Tuple
             
-- deforester

deforest (t,d) = let t' = returnval (def t EmptyCtx (free t) [] d [])
                 in  residualise t'

-- function: def t k fv m d e
-- t: current term
-- k: context
-- fv: free variables
-- m: memoised terms
-- d: function definitions
-- e: previously transformed terms

def (Free x) k fv m d e = defCtx (Free x) k fv m d e
def (Lambda x t) EmptyCtx fv m d e = let x' = renameVar fv x
                                     in  do
                                         t' <- def (concrete x' t) EmptyCtx (x':fv) m d e
                                         return (Lambda x' (abstract t' x'))
def (Lambda x t) (ApplyCtx k u) fv m d e = def (subst u t) k fv m d e
def (Lambda x t) (CaseCtx k bs) fv m d e = error "Unapplied function in case selector"
def (Con c ts) EmptyCtx fv m d e = do
                                   ts' <- defArgs ts fv m d e
                                   return (Con c ts')
def (Con c ts) (ApplyCtx k u) fv m d e = error ("Constructor application is not saturated: "++show (place (Con c ts) (ApplyCtx k u)))
def (Con c ts) (CaseCtx k bs) fv m d e = case find (\(c',xs,t) -> c==c' && length xs == length ts) bs of
                                            Nothing -> error ("No matching pattern in case for term:\n\n"++show (Case (Con c ts) bs))
                                            Just (c',xs,t) -> def (foldr subst t ts) k fv m d e
def (Apply t u) k fv m d e = def t (ApplyCtx k u) fv m d e
def (Case t bs) k fv m d e = def t (CaseCtx k bs) fv m d e
def (Fun f) k fv m d e = let t = place (Fun f) k
                         in  case [rename (fromJust r) u | u@(Unfold _ t' _) <- e, let r = renaming t' t, isJust r] of
                                (u:_) -> return u
                                [] -> fold t fv m d e
def (Let x t u) k fv m d e = let x' = renameVar fv x
                             in  do
                                 t' <- def t EmptyCtx fv m d e
                                 u' <- def (concrete x' u) k (x':fv) m d (unfolds t'++e)
                                 return (Let x t' (abstract u' x'))

defArgs [] fv m d e = return []
defArgs (t:ts) fv m d e = do
                          t' <- def t EmptyCtx fv m d e
                          ts' <- defArgs ts fv m d (unfolds t'++e)
                          return (t':ts')

defBranches [] k fv m d e = return []
defBranches ((c,xs,t):bs) k fv m d e = let xs' = renameVars fv xs
                                       in do
                                          t' <- def (foldr concrete t xs') k (xs'++fv) m d e
                                          bs' <- defBranches bs k fv m d (unfolds t'++e)
                                          return ((c,xs,foldl abstract t' xs'):bs')

defCtx t EmptyCtx fv m d e = return t
defCtx t (ApplyCtx k u) fv m d e = do
                                   u' <- def u EmptyCtx fv m d e
                                   defCtx (Apply t u') k fv m d (unfolds u'++e)
defCtx t (CaseCtx k bs) fv m d e = do
                                   bs' <- defBranches bs k fv m d e
                                   return (Case t bs')

defLet [] t fv m d e = return t
defLet ((x,t):s') u fv m d e = do
                               t'' <- def t EmptyCtx fv m d e
                               u' <- defLet s' u (x:fv) m d (unfolds t''++e)
                               return (Let x t'' (abstract u' x))

fold t fv m d e = case [(u,t') | (u,t') <- m, couple t' t] of
                     ((u,t'):_) -> let (u',s1,s2) = generalise t' t fv [] []
                                   in  case renaming t' u' of
                                          Nothing -> throw (u,(u',s1))
                                          Just r -> defLet s2 (Fold (rename r u)) fv m d e
                     [] -> let f = renameVar (fv ++ [f | (Unfold t _ _) <- e, let Fun f = redex t]) "f"
                               xs = free t
                               u = foldl (\t x -> Apply t (Free x)) (Fun f) xs
                               handler (u',(t',s')) = if   u==u'
                                                      then do
                                                           t'' <- def t' EmptyCtx (fv++map fst s') m d e
                                                           defLet s' t'' (f:fv) m d (unfolds t''++e)                                                    
                                                      else throw (u',(t',s'))
                            in  do
                                t' <- handle (def (unfold t d) EmptyCtx (f:fv) ((u,t):m) d e) handler
                                return (Unfold u t t')
