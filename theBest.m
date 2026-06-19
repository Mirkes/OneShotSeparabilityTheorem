%%%%%%%%%%%%%%%
%
% Function to calculate the best one-shot separability direction
%
% Developed by Mirkes E.M. for paper Bogdan Grechuk, Alexander N. Gorban,
% Evgeny M. Mirkes, and Ivan Y. Tyukin. One short separation theorem
%
%%%%%%%%%%%%%%%

function res = theBest(x, mu, who)
% theBest converts input vector x into vector defined by formula in
% paper or by tabulated function
%
% Inputs:
%   x is row vector (many vectors) to calculate normal.
%   mu is structure with required parameters for calculation
%   who is number of distribution in array distribs
%
% Output
%   res is normal vector (many vectors) for x.

    switch who
        case 1
            % Cauchy
            def = 1 / size(x, 2);
            res = zeros(size(x));
            for row = 1:size(x, 1)
                [ma, ind] = max(abs(x(row,:)));
                if ma == 0
                    res(row, :) = def;
                else
                    res(row, ind) = sign(x(row, ind));
                end
            end
        case 2
            % Cube
            res = interp1(mu.x, mu.c, x);
            % kill NaNs
            res(isnan(res)) = 0;
        case 3
            % Exp
            res = 1 - 1 ./ (x + 1);
            res(isnan(res)) = -10000;
        case 4
            % Gauss it is meaningless because c(x)=x
            res = x;
        case 5
            % Laplace
            res = (sqrt(1 + x .^ 2) - 1) ./ x;
            res(x == 0) = 1;
        case 6
            % Pareto
            res = interp1(mu.x, mu.c, x);
            % kill NaNs
            res(isnan(res)) = 0;
    end

    % Normalise vectors to unit length
    len = sqrt(sum(res .^ 2,  2));
    % Prevent zero division
    len(len == 0) = 1;
    res = res ./ len;
end
