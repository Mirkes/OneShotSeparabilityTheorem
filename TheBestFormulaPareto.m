%%%%%%%%%%%%%
%
% Tabulate function c(x) for the best direction for uniform in cube
%
% Developed by Mirkes E.M. for paper Bogdan Grechuk, Alexander N. Gorban,
% Evgeny M. Mirkes, and Ivan Y. Tyukin. One short separation theorem
%
%%%%%%%%%%%%%

% This script must be processed BEFORE data generation

function res = forMin(c, x, gamma)
    if c >= 0
        res = 1;
    else
        fun = @(z) exp(c * z) ./ (z .^ (gamma + 1));
        res = gamma * exp(- c * x) * integral(fun, 1, Inf);
    end
end

% General constants
gamma = 1;
% Tabulation of function from minimum of function
% Upper parameter 9.3 was found empirically
X = 1:0.001:9.3;
c = zeros(size(b));
for k = 1:length(X)
    c(k) = fminbnd(@(x) forMin(x, X(k), gamma), -1000, 0);
end

save("Pareto/TheBestForPareto.mat", "c", "X", "g");

