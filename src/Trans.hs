-- Module Trans: program transformation

module Trans where

import Term
import Exception
import Prelude hiding ((<>))
import Data.Maybe
import Data.List
import Data.Tuple
             
-- deforester

deforest (t,d) = let t' = returnval (def t EmptyCtx (free t) [] [] [] d [])
                 in  residualise t'

-- function: def t k fv m s1 s2 d e
-- t: current term
-- k: context
-- fv: free variables
-- m: memoised terms
-- s1: generalisation environment
-- s2: generalisation environment
-- d: function definitions
-- e: previously transformed terms

def (Free x) k fv m s1 s2 d e = defCtx (Free x) k fv m s1 s2 d e
def (Lambda x t) EmptyCtx fv m s1 s2 d e = let x' = renameVar fv x
                                           in  do
                                               t' <- def (concrete x' t) EmptyCtx (x':fv) m s1 s2 d e
                                               return (Lambda x' (abstract t' x'))
def (Lambda x t) (ApplyCtx k u) fv m s1 s2 d e = def (subst u t) k fv m s1 s2 d e
def (Lambda x t) (CaseCtx k bs) fv m s1 s2 d e = error "Unapplied function in case selector"
def (Con c ts) EmptyCtx fv m s1 s2 d e = do
                                         ts' <- defArgs ts fv m s1 s2 d e
                                         return (Con c ts')
def (Con c ts) (ApplyCtx k u) fv m s1 s2 d e = error ("Constructor application is not saturated: "++show (place (Con c ts) (ApplyCtx k u)))
def (Con c ts) (CaseCtx k bs) fv m s1 s2 d e = case find (\(c',xs,t) -> c==c' && length xs == length ts) bs of
                                                  Nothing -> error ("No matching pattern in case for term:\n\n"++show (Case (Con c ts) bs))
                                                  Just (c',xs,t) -> def (foldr subst t ts) k fv m s1 s2 d e
def (Apply t u) k fv m s1 s2 d e = def t (ApplyCtx k u) fv m s1 s2 d e
def (Case t bs) k fv m s1 s2 d e = def t (CaseCtx k bs) fv m s1 s2 d e
def (Fun f) k fv m s1 s2 d e = let t = place (Fun f) k
                               in  case [rename r u | u@(Unfold _ t' _) <- e, r <- renaming t' t] of
                                      (u:_) -> return u
                                      [] -> fold t fv m s1 s2 d e
def (Let x t u) k fv m s1 s2 d e = let x' = renameVar fv x
                                   in  do
                                       t' <- def t EmptyCtx fv m s1 s2 d e
                                       u' <- def (concrete x' u) k (x':fv) m s1 s2 d (unfolds t'++e)
                                       return (Let x t' (abstract u' x'))

defArgs [] fv m s1 s2 d e = return []
defArgs (t:ts) fv m s1 s2 d e = do
                                t' <- def t EmptyCtx fv m s1 s2 d e
                                ts' <- defArgs ts fv m s1 s2 d (unfolds t'++e)
                                return (t':ts')

defBranches [] k fv m s1 s2 d e = return []
defBranches ((c,xs,t):bs) k fv m s1 s2 d e = let xs' = renameVars fv xs
                                             in do
                                                t' <- def (foldr concrete t xs') k (xs'++fv) m s1 s2 d e
                                                bs' <- defBranches bs k fv m s1 s2 d (unfolds t'++e)
                                                return ((c,xs,foldl abstract t' xs'):bs')

defCtx t EmptyCtx fv m s1 s2 d e = return t
defCtx t (ApplyCtx k u) fv m s1 s2 d e = do
                                         u' <- def u EmptyCtx fv m s1 s2 d e
                                         defCtx (Apply t u') k fv m s1 s2 d (unfolds u'++e)
defCtx t (CaseCtx k bs) fv m s1 s2 d e = do
                                         bs' <- defBranches bs k fv m s1 s2 d e
                                         return (Case t bs')

defFold [] fv m s1 s2 d e = return []
defFold ((x,t):s) fv m s1 s2 d e = do
                                   t' <- def t EmptyCtx fv m s1 s2 d e
                                   s' <- defFold s fv m s1 s2 d (unfolds t'++e)
                                   return ((x,t'):s')

fold t fv m s1 s2 d e = case [(u,t',r) | (u,t') <- m, r <- embedding t' t] of
                           ((u,t',r):_) -> let (u',s1',s2') = generalise t' t fv s1 s2
                                           in  case renaming t' u' of
                                                  [] -> throw (u,(u',s1',s2'))
                                                  (r':_) -> do
                                                           s <- defFold s2' fv m s1 s2 d e
                                                           return (Fold (instantiate s (rename r (rename r' u))))
                           [] -> let f = renameVar (fv ++ [f | (Unfold t _ _) <- e, let Fun f = redex t]) "f"
                                     xs = free t
                                     u = foldl (\t x -> Apply t (Free x)) (Fun f) xs
                                     handler (u',(t',s1',s2')) = if   u==u'
                                                                 then def (makeLet s1' t') EmptyCtx (f:fv) m (s1++s1') (s2++s2') d e                                                               
                                                                 else throw (u',(t',s1',s2'))
                                   in  do
                                       t' <- handle (def (unfold t d) EmptyCtx (f:fv) ((u,t):m) s1 s2 d e) handler
                                       return (Unfold u t t')

