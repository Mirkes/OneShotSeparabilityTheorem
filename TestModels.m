%%%%%%%%%%%%%%%
%
% This script tested several models for specified distribution on the test
% set. Neuraal networks MUSt be in NNs folder of the  main folder with
% distribution name, results will be saved in the subforlder TestRes of the
% main folder 
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

%%%%%%%%%%%%%%%
%
% Functions
%
%%%%%%%%%%%%%%%

function res = universal(x)
% bogdan calculates normal vector for row vector x according to proposition
% 11 in paper.
%
% Inputs:
%   x is row vector (many vectors) to calculate normal.
%
%   res is normal vector (many vectors) for x.

    res = x ./ (1 + abs(x));
    % Normalise vectors to unit length
    len = sqrt(sum(res .^ 2, 2));
    len(len == 0) = 1;
    res = res ./ len;
end

function res = mypredict(model, X)
% mypredict calculates normal vector for vector X and specified model.
%
% Inputs:
%   model is network or other model which produced normal vector. This
%       model has dim inputs and outputs, where dim is dimension of space.
%   X is row vector (many vectors) to calculate normal.
%
%   res is normal vector (many vectors) for X.

    if ischar(model)
        model = string(model);
    end
    if isstring(model)
        % There are two possible strings
        if strcmpi(model, 'Fisher')
            res = X;
            len = sqrt(sum(res .^ 2, 2));
            res = res ./ len;
        elseif strcmpi(model, 'UniversalD')
            res = universal(X);
        end
    else
        % This section consider three possible NN but it is the saame from
        % point of view of prediction
        res = predict(model, X);
    end
end

function res = testNetOvA(net, data, ~)
% testNetOvA get set of points and tested separation of each point from all
% other points. If point is not separated from all other points, then point
% considered as inseparable.
%
% Inputs:
%   net is network with dim inputs and outputs, wheredim is dimension of
%       space
%   data is matrix of points with one point per row.
%   mu is distribution specific set of parameters
%
% Output:
%   res is 1 if set is inseparable and 0 otherwise.

    % Get normal for each vector
    norm = mypredict(net, data);
    % Calculate dot product of each point with normal of the same point
    summ2 = (sum(data .* norm, 2))';

    % Start to calculate part 1
    maxN = size(data, 1);
    STEP = 5000;
    for k = 1:10000:maxN
        kk = k + STEP - 1;
        if kk > maxN
            kk = maxN;
        end
        for n = 1:10000:maxN
            nn = n + STEP - 1;
            if nn > maxN
                nn = maxN;
            end
            % Calculate dot products of all vectors with all normals
            res = data(k:kk, :) * norm(n:nn, :)' - summ2(n:nn);
            if k == n
                % diagonal fragment
                res = res - diag(diag(res));
            end
            res = res > 0;
            if any(res > 0, "all")
                res = 1;
                return
            end
        end
    end
    res = 0;
end

function vals = testOneM(data, m, models, nTests, mu)
    setSizes = size(data, 1);
    nMod = length(models);
    % create array for separability recording
    seps = zeros(nTests, nMod);
    parfor t = 1:nTests
        ind = randperm(setSizes, m);
        sets = data(ind, :); %#ok<PFBNS>
        for mods = 1:nMod
            if testNetOvA(models{mods}, sets, mu) > 0 %#ok<PFBNS>
                seps(t, mods) = 1;
            end
        end
    end
    % Calculate statistics
    vals = 1 - sum(seps, 1) / nTests;
end

%%%%%%%%%%%%%%%
%
% Calculations itself
%
%%%%%%%%%%%%%%%

distr = distribs(dists);

% Dimensions
dims = [5:15, 20:5:80]';
nDim = length(dims);

% Models
models = {"theBest", "Fisher", "LNN", "NLNN", "UniversalD", "BNN"};
nMod = length(models);

% Load data
load(distr + "/" + distr + "AllData.mat", "testSet", "mu");
% File names for usage
savFileDraft = distr + "/TestRes/data_%d.mat";
linFish = distr + "/NNs/Dim_%d_Fisher.mat";
linOther = distr + "/NNs/Dim_%d.mat";
nlinFish = distr + "/NNs/NLDim_%d_Fisher.mat";
nlinOther = distr + "/NNs/NLDim_%d.mat";
bNNFileDraft = distr + "/NNs/theBestNN_%d.mat";


% Number of points in test set
setSize = size(testSet, 1);
% Maximal cardinality of tested set  
maxSize = round(setSize * 0.75);
% The number of sets of the same cardinality to test
nTests = 10000;
% Required probability 

% Calculate theoretical estimation of maximal separable set
ests = theoreticValues(dists, dims, p);

% Main loop
for d = 1:nDim
    % data for test
    dim = dims(d);
    % Theoretical estimation of value
    est = ests(d);
    fprintf("Dimension %d, predicted threshold %d\n", dim, est);
    if est < 2
        est = 2;
    end
    
    tstSet = testSet(:, 1:dim);

    % Get linear NN model
    load(sprintf(linFish, dim));
    load(sprintf(linOther, dim));
    if accVal < bestVal
        models(3) = {bestN};
    else
        models(3) = {net};
    end
    % Get nonlinear NN model
    load(sprintf(nlinFish, dim));
    load(sprintf(nlinOther, dim));
    if accVal < bestVal
        models(3) = {bestN};
    else
        models(3) = {net};
    end
    % Get the best direction NN model
    load(sprintf(bNNFileDraft, dim));
    models(4) = {bestB};

    % File name for work
    fNameRes = sprintf(saveFileDraft, dim);

    % do not repeat previously completed calculations
    if isfile(fNameRes)
        load(fNameRes)
        fprintf("Dimension %d Last cardinality %d the best %.3f Fisher"+...
            " %.3f LNN %.3f NLNN %.3f UniD %.3f bestNN %.3f\n", ...
            dim, mypool(end, :));
    else
        mypool = [est, testOneM(tstSet, est, models, nTests, mu)];
        fprintf("Dimension %d Start cardinality %d the best %.3f Fisher"+...
            " %.3f LNN %.3f NLNN %.3f UniD %.3f bestNN %.3f\n", ...
            dim, mypool(end, :));
        save(fNameRes, "mypool");
    end

    % Now we search minimal set to start data collection We dectrease
    % cardinality up to size where all models have appropriate probability.
    while mypool(1, 1) > 2 && any(mypool(1, 2:end) < p)
        % Decrease cardinality by 10%
        q = round(mypool(1, 1) / 1.1);
        % Decreasing must be at least 1.
        if q == mypool(1, 1)
            q = q - 1;
        end
        
        tmp = [q, testOneM(tstSet, q, models, nTests, mu)];
        mypool = [tmp; mypool]; %#ok<AGROW>
        fprintf("Dimension %d Decreasing cardinality %d the best %.3f"+...
            " Fisher %.3f LNN %.3f NLNN %.3f UniD %.3f bestNN %.3f\n", ...
            dim, tmp);
        save(fNameRes, "mypool");
    end

    % Search of the last m where probability is greater or equal to p
    % for at least one of model
    while mypool(end, 1) < maxSize && any(mypool(end, 2:end) > p)
        % Increase cardinality by 10%
        q = round(mypool(end, 1) * 1.1);
        % Increasing must be at least 1.
        if q == mypool(end, 1)
            q = q + 1;
        end
        tmp = [q, testOneM(tstSet, q, models, nTests, mu)];
        fprintf("Dimension %d Increasing cardinality %d the best %.3f"+...
            " Fisher %.3f LNN %.3f NLNN %.3f UniD %.3f bestNN %.3f\n", ...
            dim, tmp);
        mypool = [mypool; tmp]; %#ok<AGROW>
        save(fNameRes, "mypool");
    end
end
