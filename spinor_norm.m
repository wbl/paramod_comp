 intrinsic Reflect(v,N) -> AlgMatElt
     { Compute reflection of V with norm N }
     n:=Ncols(v);
     ret:=ZeroMatrix(Rationals(), n, n);
     for i in [1..n] do
	 w:=ZeroMatrix(Rationals(), 1, n);
	 w[1,i]:=1;
	 num:=2*w*N*Transpose(v)*(v*N*(Transpose(v)))^(-1);
	 ret[i]:=(w-num*v)[1];
     end for;
     assert ret*N*Transpose(ret) eq N;
     return ret;
 end intrinsic;
//Implementation of spinor norm calculations
 intrinsic SpinorNorm(M::Mtrx, V::Mtrx) -> Rational
     { Compute the spinor norm of the isometry M with the inner product V }
     n:=Ncols(M);
     V:=MatrixRing(Rationals(),n)!V;
     M:=MatrixRing(Rationals(),n)!M;
     assert M*V*Transpose(M) eq V;
     G, T, _ := OrthogonalizeGram(V);
     //Rows of T are an orthonormal basis for original inner product: apply
     //algorithm
     retval:=Matrix(Rationals(), 1, 1, [1]);
     transform:=M;
     for i in [1..n] do
	 vec := T[i];
	 tmp := vec*transform-vec;
	 asb:=ZeroMatrix(Rationals(), 1, n);
	 asb[1]:=tmp;
	 if not (asb eq 0) then
	     transform:=transform*Reflect(asb, V);
	     retval := retval*asb*V*Transpose(asb);
	 end if;
     end for;
     return retval[1,1];
 end intrinsic;

 intrinsic SqRatClass(x::FldRatElt)->FldRatElt
     { Obvious element in square class of a rational }
     return Squarefree(Numerator(x))*Squarefree(Denominator(x));
 end intrinsic;

 intrinsic ThetaIsoms(N::Lat)-> []
     { Compute theta of isometries of N }
     if assigned N`ThetaIsoms then
	 return N`ThetaIsoms;
     end if;
     B:=Matrix(Rationals(), BasisMatrix(N));
     inner:=Matrix(Rationals(), InnerProductMatrix(N));
     retval:=[];
     for T in Generators(AutomorphismGroup(N)) do
	 if Determinant(T) eq 1 then
	     Append(~retval, SqRatClass(SpinorNorm(B^(-1)*Matrix(Rationals(), T)*B, 1/2*inner)));
	 else
	     Append(~retval, SqRatClass(SpinorNorm(-1*B^(-1)*Matrix(Rationals(), T)*B, 1/2*inner)));
	 end if;
     end for;
     N`ThetaIsoms := retval;
     return retval;
 end intrinsic;
 
 intrinsic ThetaEquivalent(M::Lat, N::Lat)->Bool
     { Determine of M and N are theta-equivalent }
     assert InnerProductMatrix(M) eq InnerProductMatrix(N);
     test, T :=IsIsometric(M,N);
     if test eq false then
	 return false;
     end if;
     //TODO: cache theta image of automorphism group via some structs
     B1:=Matrix(Rationals(),BasisMatrix(M));
     B2:=Matrix(Rationals(), BasisMatrix(N));
     T:=Matrix(Rationals(), T);
     //T takes coordinates on N and turns them to coordinates on M
     ambient_iso:=B2^(-1)*T*B1;
     if Determinant(ambient_iso) eq -1 then
	 ambient_iso := -1*ambient_iso;
     end if;
     assert ambient_iso*InnerProductMatrix(M)*Transpose(ambient_iso) eq InnerProductMatrix(M);
     theta:=SqRatClass(SpinorNorm(ambient_iso, 1/2*InnerProductMatrix(M)));
     //Use isometries on N to reduce: cf Tornaria thesis
     //This is what we want to cache
     //Are we sure we used the right one...?
     im_aut:=ThetaIsoms(N);
     //Now decide if theta is in the image of im_aut via linear algebra;
     if #im_aut eq 0 then
	 return theta eq 1;
     end if;
     if not(PrimeFactors(theta) subset PrimeFactors(&* im_aut)) then
	 return false;
     end if;
     primes:=PrimeFactors(&* im_aut);
     n:=#primes;
     mat:=ZeroMatrix(GaloisField(2), #im_aut, n);
     vec:=Vector(GaloisField(2), #primes, [0 : i in primes]);
     i:=1;
     for p in primes do
	 j:=1;
	 for im in im_aut do
	     if (im mod p) eq 0 then
		 mat[j, i]:= 1;
	     end if;
	     j := j+1;
	 end for;
	 if (theta mod p) eq 0 then
	     vec[i]:=1;
	     i:=i+1;
	 end if;
     end for;
     if IsConsistent(mat, vec) then
	 return true;
     else
	 return false;
     end if;
 end intrinsic;

 intrinsic VectWNorm(V, p)-> AlgMatElt
     { Return vector of norm p}
     J:=DiagonalJoin(V, Matrix(Rationals(), 1, 1, [-p]));
     n:=Ncols(J);
     vec:=BasisMatrix(IsotropicSubspace(J));
     for row in Rows(vec) do
	 if not(row[n] eq 0) then
	     retval:=Matrix(Rationals(), 1, n-1, [row[i]/row[n]: i in [1..n-1]]);
	     assert (retval*V*Transpose(retval))[1,1] eq p;
	     return retval, true;
	 end if;
     end for;
     return false, false;
end intrinsic;

//Todo: make reliable
intrinsic SpinorOperation(M::Lat, p)-> Lat
    { Act on the basis of M by reflection by a vector of norm p }
    Qform:=1/2*InnerProductMatrix(M);
    veca, succa:=VectWNorm(Qform, 2);
    vecb, succb:=VectWNorm(Qform, 2*p);
    if succa and succb then
	transform:=Reflect(veca, Qform)*Reflect(vecb, Qform);
    else
	assert false; 
    end if;
    basis:=Matrix(Rationals(),BasisMatrix(M));
    lat:=LatticeWithBasis(basis*transform, 2*Qform);
    return lat;
end intrinsic;
