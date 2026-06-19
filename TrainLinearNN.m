%%%%%%%%%%%%%
%
% Train linear network. Do not forgot to create folder NNs
% in main folder of used distribution.
%
% Developed by Mirkes E.M. for paper Bogdan Grechuk, Alexander N. Gorban,
% Evgeny M. Mirkes, and Ivan Y. Tyukin. One short separation theorem
%
%%%%%%%%%%%%%

distribs = ["Cauchy", "Cube", "Exp", "Gauss", "Laplace", "Pareto"];

% Specify number of distribution. If you want to add new distribution, you
% should add distribution's name to distribs and add corresponding content
% for function theBest.m

dists = 5; 

distr = distribs(dists);

% Dimensions to train NN
dims = [5:15, 20:5:80]';
nDim = length(dims);

% For different size of networks
maxSize = 5;
% Number of NNs to select the best
nNN = 100;
% File names
fisherDraft = distr + "/NNs/" + "Dim_%d_Fisher.mat";
otherDraft = distr + "/NNs/" + "Dim_%d.mat";

% Load data
load(distr + "/" + distr + 'AllData.mat');

% Training set size
trSetSize = size(trSets1, 1);

% form labels to train NN. We want to have all cases of class 2
labels = [zeros(trSetSize, 1), ones(trSetSize, 1)];

for d = 1:nDim
    dim = dims(d);
    fprintf("Dimension %d\n", dim);

    % Get required dimension
    trSet1 = trSets1(:, 1:dim);
    trSet2 = trSets2(:, 1:dim);
    valSet1 = valSets1(:, 1:dim);
    valSet2 = valSets2(:, 1:dim);

    % Form datastore
    dsX1Tr = arrayDatastore(trSet1);
    dsX2Tr = arrayDatastore(trSet2);
    dsT = arrayDatastore(labels);
    dsX1Val = arrayDatastore(valSet1);
    dsX2Val = arrayDatastore(valSet2);

    % Combine datastores
    dsTrain = combine(dsX1Tr, dsX2Tr, dsT);
    dsVal = combine(dsX1Val, dsX2Val, dsT);

    % Create and train Linear Fisher NN
    % Create layers for NN
    layers = [featureInputLayer(dim, Name="internalNetIn"), ...
        fullyConnectedLayer(dim, 'Name', 'internalNet1'), ...
        functionLayer(@(X) (X ./ vecnorm(X)))];

    % Initialise Linear Fisher NN
    layers(2).Weights = eye(dim);
    lgraph = layerGraph(layers);
    res = dlnetwork(lgraph);
    
    % Training options
    options = trainingOptions("lbfgs", ...
        ExecutionEnvironment="cpu", ...
        Plots="none",... %"training-progress", ...
        ValidationData = dsVal, ... 
        ValidationFrequency = 1, ...
        ValidationPatience = 6, ...
        StepTolerance = 1.e-10, ...
        Verbose=true, ...
        VerboseFrequency=1);

    % Create network
    net = separativeFNN(dim, true, res);
    % Train network
    [net, info] = trainnet(dsTrain, net, "crossentropy", options);
    % Extract required NN
    net = extractionFromSNN(net);
    % estimate accuracies for train and validation sets
    accTr = assessAcc(net, trSet1, trSet2);
    accVal = assessAcc(net, valSet1, valSet2);
    fprintf("Accuracies of Fisher's started network are training %.4f,"+...
        " validation %.4f\n", accTr, accVal);
    % Save result
    save(sprintf(fisherDraft, dim), "net", "accTr", "accVal");

    bestN = 0;
    bestVal = 0;
    bestTr = 0;
    for k = 1:nNN
        % Create and train Linear NN with random start
        layers(2).Weights = rand(dim);
        lgraph = layerGraph(layers);
        res = dlnetwork(lgraph);
        
        % Create normalised network
        net = separativeFNN(dim, true, res);
        % Train network
        [net, info] = trainnet(dsTrain, net, "crossentropy", options);
        % Extract required NN
        net = extractionFromSNN(net);
        % estimate accuracies
        accTr = assessAcc(net, trSet1, trSet2);
        accVal = assessAcc(net, valSet1, valSet2);
        fprintf("NN %d/%d Accuracies of randomy started network are" +...
            " training %.4f, validation %.4f, best validation %.4f\n", ...
            k, nNN, accTr, accVal, bestVal);
        if bestVal < accVal
            bestVal = accVal;
            bestTr = accTr;
            bestN = net;
        end
        % If the best NN have the perfect result then stop.
        if bestVal == 1
            break
        end
    end

    % Save result
    save(sprintf(otherDraft, dim), "bestN", "bestTr", "bestVal");
end


