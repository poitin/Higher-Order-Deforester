module Trans where

import Term
import Exception
import Data.List
import Data.Maybe
import Debug.Trace

def (t,d) = returnval (deforest t EmptyCtx (free t) [] d)

deforest t (ApplyCtx k []) fv m d = deforest t k fv m d
deforest (Free x) k fv m d = deforestCtx (Free x) k fv m d
deforest (Lambda x t) EmptyCtx fv m d = let x' = rename fv x
                                        in do
                                           t' <- deforest (concrete x' t) EmptyCtx (x':fv) m d
                                           return (Lambda x (abstract t' x'))
deforest (Lambda x t) (ApplyCtx k (t':ts)) fv m d = deforest (subst t' t) (ApplyCtx k ts) fv m d
deforest (Lambda x t) (CaseCtx k bs) fv m d = error "Unapplied function in case selector"
deforest (Con c ts) EmptyCtx fv m d = do
                                      ts' <- mapM (\t -> deforest t EmptyCtx fv m d) ts
                                      return (Con c ts')
deforest (Con c ts) (ApplyCtx k ts') fv m d = error ("Constructor application is not saturated: "++show (place (Con c ts) (ApplyCtx k ts')))
deforest (Con c ts) (CaseCtx k bs) fv m d = case find (\(c',xs,t) -> c==c' && length xs == length ts) bs of
                                               Nothing -> error ("No matching pattern in case for term:\n\n"++show (Case (Con c ts) bs))
                                               Just (c',xs,t) -> deforest (foldr subst t ts) k fv m d
deforest (Fun f) k fv m d | f `notElem` fst(unzip d) = deforestCtx (Fun f) k fv m d
deforest (Fun f) k fv m d = let t = place (Fun f) k
                            in case find (\(f,(xs,t')) -> isJust (inst t' t)) m of
                                  Just (f,(xs,t')) -> let Just s = inst t' t
                                                      in  deforest (makeLet s (Apply (Fun f) (map Free xs))) EmptyCtx fv m d
                                  Nothing -> case find (\(f,(xs,t')) -> not (null (embed t' t))) m of
                                                Just (f,_) -> throw (f,t)
                                                Nothing -> let fs = fst(unzip(m++d))
                                                               f = rename fs "f"
                                                               xs = free t
                                                               (t',d') = unfold t (f:fs) d
                                                               handler (f',t') = if   f==f'
                                                                                 then let (t'',s1,s2) = generalise t t'
                                                                                      in  deforest (makeLet s1 t'') EmptyCtx fv m d
                                                                                 else throw (f',t')
                                                           in  do t'' <- handle (deforest t' EmptyCtx fv ((f,(xs,t)):m) d') handler
                                                                  return (if f `elem` funs t'' then Letrec f xs (foldl abstract (abstractFun t'' f) xs) (Apply (Bound 0) (map Free xs)) else t'')

deforest (Apply t ts) k fv m d = deforest t (ApplyCtx k ts) fv m d
deforest (Case t bs) k fv m d = deforest t (CaseCtx k bs) fv m d
deforest (Let x t u) k fv m d = let x' = rename fv x
                                in do
                                   t' <- deforest t EmptyCtx fv m d
                                   u' <- deforest (concrete x' u) k (x':fv) m d
                                   return (subst t' (abstract u' x'))
deforest (Letrec f xs t u) k fv m d = let f' = rename (fst(unzip(m++d))) f
                                          t' = concreteFun f' (foldr concrete t xs)
                                          u' = concreteFun f' u
                                      in  deforest u' k fv m ((f',(xs,t')):d)

deforestCtx t EmptyCtx fv m d = return t
deforestCtx t (ApplyCtx k ts) fv m d = do
                                       ts' <- mapM (\t -> deforest t EmptyCtx fv m d) ts
                                       deforestCtx (Apply t ts') k fv m d
deforestCtx t (CaseCtx k bs) fv m d = do
                                      bs' <- mapM (\(c,xs,t) -> let fv' = foldr (\x fv -> let x' = rename fv x in x':fv) fv xs
                                                                    xs' = take (length xs) fv'
                                                                in do
                                                                   t' <- deforest (foldr concrete t xs') k fv' m d
                                                                   return (c,xs,foldl abstract t' xs')) bs
                                      return (Case t bs')

