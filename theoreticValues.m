%%%%%%%%%%%%%%%
%
% Calculate theoretical estimation of maximal separable set
%
% Developed by Mirkes E.M. for paper Bogdan Grechuk, Alexander N. Gorban,
% Evgeny M. Mirkes, and Ivan Y. Tyukin. One short separation theorem
%
%%%%%%%%%%%%%%%

function res = theoreticValues(who, x, p)
% theoreticValues calculates theoretical estimation of values for
% separability with probability p.
%
% Inputs:
%   who is the number of distribution
%   x is vector of dimensions to use
%   p is probability to use
%   
% Output:
%   res is vector of estimated values, has the same size as vector dims

    delta = 1 - p;
    switch who
        case 1 % Cauchy
            res = ones(size(dims));
        case 2 % Cube
            res = sqrt(delta / 1) * exp(0.2468 * x);        
        case 3 % Exp
            res = sqrt(delta / 1) * exp(0.1931 * x);
        case 4 % Gauss
            res = sqrt(delta / 1) * exp(0.1732 * x);
        case 5 % Laplace
            res = sqrt(delta / 1) * exp(0.1195 * x);
        case 6 % Pareto
            res = sqrt(delta / 1) * exp(0.1547 * x);
    end

    res = ceil(res);
end