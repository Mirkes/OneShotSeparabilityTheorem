%%%%%%%%%%%%%%%
%
% Collect results of model testing and form one file with aggregated data
%
% Developed by Mirkes E.M. for paper Bogdan Grechuk, Alexander N. Gorban,
% Evgeny M. Mirkes, and Ivan Y. Tyukin. One short separation theorem
%
%%%%%%%%%%%%%%%

distribs = ["Cauchy", "Cube", "Exp", "Gauss", "Laplace", "Pareto"];

% Specify number of distribution. If you want to add new distribution, you
% should add distribution's name to distribs and add corresponding blocks
% to some functions.

dists = 5;

% Required probability of separability
p = 0.99;

distr = distribs(dists);

% Initially use all dimensions but part of them can be removed if models or
% linear separability test will be not processed for high dimensions
dims = [5:15, 20:5:80]';

models = {"theBest", "Fisher", "LNN", "NLNN", "UniversalD", "BNN"};
% Target list of models is
%   1. Theory 
%   2. Universal boundary
%   3. Empirical one-shot
%   4. Fisher
%   5. General linear
%   6. Nonlinear neural network
%   7. Universal sigmoid formula

% Place to put read model. 0 means omit.
toPut = [3, 4, 0, 6, 7, 0];

nameToSave = distr + "/SetData.mat";
inpFileDraft = distr + "/TestRes/data_%d.mat";
linSepDraft = distr + "/TestRes/LinSep_%d.mat";

% assemble data
nDim = length(dims);
res = zeros(nDim, 7);
nMod = length(models);

% The first is theory
res(:, 1) = theoreticValues(dists, dims, p);
res(:, 2) = universalBoundary(dims, p);

last = 0;
for d = 1:nDim
    dim = dims(d);
    % Results of TestModels
    % form file name
    fName = sprintf(inpFileDraft, dim);
    if ~isfile(fName)
        % there is no such data. Stop
        break
    end
    load(fName);
    for k = 1:nMod
        if toPut(k) == 0
            continue
        end
        pos = find(mypool(:, k) > p, 1, 'last');
        if isempty(pos)
            res(d, toPut(k)) = 1;
        else
            res(d, toPut(k)) = mypool(p, 1);
        end
    end
    last = last + 1;
    % Results of Linear separability
    fName = sprintf(linSepDraft, dim);
    if ~isfile(fName)
        fprintf("For dimension %d there are results of TestModels but"+...
            " there is no result of Linear separability test", dim);
        % there is no such data. Stop
        continue
    end
end

dims =  dims(1:last);
res = res(1:last,:);
% Save colleted data
save(nameToSave, "res", "dims");

